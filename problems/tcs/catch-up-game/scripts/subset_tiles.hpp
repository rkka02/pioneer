#pragma once
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <thread>
#include <vector>

namespace catchup {
inline unsigned tile_bits(unsigned bits) { return std::min(7u,bits); }

// Every immediate submask is in an earlier tile rank or earlier in the same
// tile. Joining each rank keeps all row reads free of concurrent writes.
template <class F> void subset_tiles(unsigned bits, unsigned workers, F visit) {
    const unsigned high_bits=tile_bits(bits);
    const std::uint64_t width=std::uint64_t{1}<<(bits-high_bits);
    for (unsigned rank=0;rank<=high_bits;++rank) {
        std::vector<unsigned> tiles;
        for (unsigned t=0;t<(1u<<high_bits);++t)
            if (static_cast<unsigned>(__builtin_popcount(t))==rank) tiles.push_back(t);
        std::atomic<std::size_t> next{0};
        auto work=[&] {
            for (auto j=next.fetch_add(1);j<tiles.size();j=next.fetch_add(1)) {
                const unsigned t=tiles[j];
                visit(t,t*width,(t+1)*width);
            }
        };
        std::vector<std::thread> pool;
        for (std::size_t i=1;i<std::min<std::size_t>(workers,tiles.size());++i) pool.emplace_back(work);
        work();
        for (auto& t:pool) t.join();
    }
}
}
