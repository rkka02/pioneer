// Independent bottom-up table for every subset and every deficit 0..N.
// One row is eight bytes. Compile with Clang or GCC using -std=c++17 -O3.
#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

using Bits = std::uint32_t;
struct Row { Bits win, loss; };

static Bits reverse_bits(Bits x) {
#if defined(__clang__)
    return __builtin_bitreverse32(x);
#else
    x = ((x & 0x55555555u) << 1) | ((x >> 1) & 0x55555555u);
    x = ((x & 0x33333333u) << 2) | ((x >> 2) & 0x33333333u);
    x = ((x & 0x0f0f0f0fu) << 4) | ((x >> 4) & 0x0f0f0f0fu);
    return __builtin_bswap32(x);
#endif
}

static char outcome(Row row, int d) {
    const Bits bit = Bits{1} << d;
    return row.win & bit ? 'W' : row.loss & bit ? 'L' : 'D';
}

static void prefix(const Row *table, int n) {
    const Bits full = (Bits{1} << n) - 1;
    std::cout << n << '\t' << n * (n + 1) / 2 << '\t' << outcome(table[full], 0) << '\t';
    for (int x = 1; x <= n; ++x) {
        const char child = outcome(table[full ^ (Bits{1} << (x - 1))], x);
        std::cout << (child == 'W' ? 'L' : child == 'L' ? 'W' : 'D');
    }
    std::cout << std::endl;
}

static void anchor_report(const Row *table, int n) {
    if (n < 3 || (n * (n+1) / 2) % 2) return;
    const Bits full = (Bits{1} << n) - 1;
    const auto token = [](int x) { return Bits{1} << (x-1); };
    const auto index = [](char v) { return v == 'W' ? 0 : v == 'D' ? 1 : 2; };
    std::cout << n;
    for (int a : {1, 2}) {
        std::array<int, 3> count{};
        for (int b = a+1; b <= n; ++b) {
            if (b == 2*a) continue;
            const Bits rest = full ^ token(a) ^ token(b) ^ token(b-a);
            ++count[index(outcome(table[rest], 0))];
        }
        for (int c : count) std::cout << '\t' << c;
    }
    std::cout << '\t' << outcome(table[full ^ token(1) ^ token(2)], 1) << '\t';
    if (n >= 4) std::cout << outcome(table[full ^ token(2) ^ token(4)], 2);
    else std::cout << '-';
    std::array<int, 3> deleted{};
    for (int a = 1; a <= n; ++a) {
        for (int b = a+2; b <= n; b += 2)
            ++deleted[index(outcome(table[full ^ token(a) ^ token(b)], 0))];
    }
    for (int c : deleted) std::cout << '\t' << c;
    std::cout << std::endl;
}

template <std::size_t Width> struct Half {
    int sum = 0;
    std::bitset<Width> reachable;
};

template <std::size_t Width>
static std::vector<Half<Width>> subset_sums(int count, int offset) {
    std::vector<Half<Width>> half(Bits{1} << count);
    half[0].reachable.set(0);
    for (Bits mask = 1; mask < half.size(); ++mask) {
        const auto &previous = half[mask & (mask-1)];
        const int x = offset + __builtin_ctz(mask) + 1;
        half[mask].sum = previous.sum + x;
        half[mask].reachable = previous.reachable | (previous.reachable << x);
    }
    return half;
}

// Evaluate partitionability independently of the game tree, for every even-sum
// board including draws. Split [1,n] in half; the low half sums to at most 105.
static void census(const Row *table, int n) {
    const int k = n/2, low_max = k*(k+1)/2;
    const auto lows = subset_sums<106>(k, 0);
    const auto highs = subset_sums<407>(n-k, k);
    std::array<std::array<std::uint64_t, 5>, 29> counts{};
    std::array<std::array<Bits, 2>, 29> witness{};
    for (Bits hi = 0; hi < highs.size(); ++hi) {
        const auto &high = highs[hi];
        std::array<std::bitset<106>, 106> partners{};
        for (int t = high.sum % 2; t <= low_max; t += 2) {
            const int half_total = (t + high.sum)/2;
            for (int x = std::max(0, half_total-high.sum); x <= std::min(t, half_total); ++x)
                if (high.reachable[half_total-x]) partners[t].set(x);
        }
        const int high_size = __builtin_popcount(hi);
        for (Bits lo = 0; lo < lows.size(); ++lo) {
            const auto &low = lows[lo];
            if ((low.sum + high.sum) % 2) continue;
            const bool balanced = (low.reachable & partners[low.sum]).any();
            const Bits mask = (hi << k) | lo;
            const int size = high_size + __builtin_popcount(lo);
            const char value = outcome(table[mask], 0);
            if (!balanced && value == 'D') throw std::logic_error("unpartitionable draw");
            const int column = balanced ? (value == 'W' ? 2 : value == 'D' ? 3 : 4)
                                        : (value == 'W' ? 0 : 1);
            ++counts[size][column];
            if (value != 'D') {
                Bits &example = witness[size][value == 'L'];
                if (!example) example = mask;
            }
        }
    }
    std::cout << "size\tunsplit_W\tunsplit_L\tsplit_W\tsplit_D\tsplit_L\tW_mask\tL_mask\n";
    for (int size = 0; size <= n; ++size) {
        std::cout << size;
        for (auto number : counts[size]) std::cout << '\t' << number;
        std::cout << '\t' << witness[size][0] << '\t' << witness[size][1] << '\n';
    }
}

static void dense_openings(const Row *table, int n) {
    struct Counts {
        std::uint64_t wins = 0, draws = 0, losses = 0, has_one = 0, one_loses = 0;
        Bits example = 0;
    };
    std::array<Counts, 29> counts{};
    for (Bits mask = 1; mask < (Bits{1} << n); ++mask) {
        const int largest = 32-__builtin_clz(mask);
        if (3*__builtin_popcount(mask) <= 2*largest+1 || __builtin_parity(mask & 0x55555555u)) continue;
        auto &row = counts[largest];
        const char result = outcome(table[mask], 0);
        if (result == 'W') ++row.wins;
        else if (result == 'D') ++row.draws;
        else ++row.losses;
        if (mask & 1) {
            ++row.has_one;
            if (outcome(table[mask ^ 1], 1) == 'W') {
                ++row.one_loses;
                if (!row.example) row.example = mask;
            }
        }
    }
    std::cout << "maximum\tW\tD\tL\thas_one\topening_one_loses\tfirst_loss_mask\n";
    for (int largest = 1; largest <= n; ++largest) {
        const auto &r = counts[largest];
        std::cout << largest << '\t' << r.wins << '\t' << r.draws << '\t' << r.losses << '\t'
                  << r.has_one << '\t' << r.one_loses << '\t' << r.example << '\n';
    }
}

int main(int argc, char **argv) {
    try {
        if (argc < 2 || argc > 3)
            throw std::runtime_error("usage: retrograde N [--dump|--anchors|--census|--density]");
        const int n = std::stoi(argv[1]);
        if (n < 0 || n > 28) throw std::runtime_error("N must be 0..28 (2 GiB for N=28)");
        const std::string mode = argc == 3 ? argv[2] : "";
        const bool dump = mode == "--dump", anchors = mode == "--anchors", tally = mode == "--census";
        const bool dense = mode == "--density";
        if (!mode.empty() && !dump && !anchors && !tally && !dense) throw std::runtime_error("unknown option");
        const Bits end = Bits{1} << n;
        std::unique_ptr<Row[]> table(new Row[end]);
        table[0] = {0, ~Bits{1}}; // An empty board draws at zero and loses at positive deficits.
        if (mode.empty()) prefix(table.get(), 0);
        for (Bits mask = 1; mask < end; ++mask) {
            Row best{0, ~Bits{0}};
            for (Bits moves = mask; moves; moves &= moves - 1) {
                const Bits bit = moves & -moves;
                const int x = __builtin_ctz(bit) + 1;
                const Row child = table[mask ^ bit];
                // For d>x shift positive child deficits up by x. For d<=x reflect
                // about x and exchange win with loss, including the equality bit.
                const Bits win = ((child.win & ~Bits{1}) << x) | (reverse_bits(child.loss) >> (31 - x));
                const Bits loss = ((child.loss & ~Bits{1}) << x) | (reverse_bits(child.win) >> (31 - x));
                best.win |= win;
                best.loss &= loss;
            }
            table[mask] = best;
            if ((mode.empty() || anchors) && !(mask & (mask + 1))) {
                const int size = __builtin_popcount(mask);
                if (anchors) anchor_report(table.get(), size); else prefix(table.get(), size);
            }
        }
        if (tally) census(table.get(), n);
        if (dense) dense_openings(table.get(), n);
        if (dump) {
            for (Bits mask = 0; mask < end; ++mask) {
                std::cout << mask << '\t';
                for (int d = 0; d <= n; ++d) std::cout << outcome(table[mask], d);
                std::cout << '\n';
            }
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
