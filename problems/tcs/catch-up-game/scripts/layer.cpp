// Exact density census at a specified maximum. Sweep the same table twice,
// first without the maximum, then with it. All deficits have the parity of
// the remaining sum. Only the full-key rows of strict subboards are read.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>
#include "subset_tiles.hpp"

using Mask = std::uint64_t;
using Bits = std::uint32_t;
struct Row { Bits acts, waits; };

static inline void include(Row& r, Row child, unsigned x, unsigned p) {
    const unsigned c=p^(x&1), shift=(x+c)/2, cross=31-(x-c)/2;
    const Bits a=c ? child.acts : child.acts & ~(Bits{1}<<31);
    const Bits b=c ? child.waits : child.waits & ~Bits{1};
    r.acts |= (a >> shift) | (child.waits << cross);
    r.waits &= (b << shift) | (child.acts >> cross);
}

int main(int argc, char** argv) {
    try {
        if (argc!=3) throw std::runtime_error("layer maximum workers");
        const int top=std::stoi(argv[1]), workers=std::stoi(argv[2]);
        if (top<2 || top>33 || workers<1 || workers>32) throw std::runtime_error("need maximum 2..33 and workers 1..32");
        const Mask limit=Mask{1}<<(top-1);
        std::unique_ptr<Row[]> table(new Row[limit]);
        const unsigned tile_bits=catchup::tile_bits(top-1);
        int k=1;
        while (k*(k+1)/2<top) ++k;
        const Mask small_bank=(Mask{1}<<k)-1;
        // Counts are local to a tile. Three columns are mover win, draw, loss.
        std::vector<std::array<std::uint64_t,6>> counts(1<<tile_bits);
        for (bool topped:{false,true}) {
            catchup::subset_tiles(top-1,workers,[&](unsigned tile,Mask start,Mask end) {
                for (Mask s=start;s<end;++s) {
                    if (!s && !topped) {table[0]={Bits{1}<<31,~Bits{0}}; continue;}
                    const unsigned p=__builtin_parityll(s & UINT64_C(0x5555555555555555)) ^ (topped && (top&1));
                    Row r{0,~Bits{0}};
                    if (topped) include(r,table[s],top,p);
                    for (Mask m=s;m;m&=m-1) {
                        const Mask bit=m & -m;
                        include(r,table[s^bit],1+__builtin_ctzll(bit),p);
                    }
                    table[s]=r;
                    if (topped && !p) {
                        const int v=!(r.waits&1) ? 0 : (r.acts>>31) ? 1 : 2;
                        if (3*(1+__builtin_popcountll(s))>2*top+1) ++counts[tile][v];
                        if (k<top && (s & small_bank)==small_bank) ++counts[tile][3+v];
                    }
                }
            });
        }
        std::array<std::uint64_t,6> totals{};
        for (auto& tile:counts) for (int i=0;i<6;++i) totals[i]+=tile[i];
        std::cout<<top;
        for (auto c:totals) std::cout<<' '<<c;
        std::cout<<std::endl;
    } catch (const std::exception& e) {
        std::cerr<<e.what()<<'\n'; return 1;
    }
}
