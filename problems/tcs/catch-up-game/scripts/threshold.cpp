// Exact null-window minimax. Both predicates are memoized by full key.
// Build: clang++ -O3 -march=native -std=c++17 scripts/threshold.cpp -o /tmp/catch-threshold
#include <algorithm>
#include <array>
#include <utility>
#include <cstdint>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::uint64_t;

class Solver {
    std::vector<int> weights;
    std::vector<Word> cache;
    unsigned gap_bits = 1;
    bool small_first;
    using Gaps = std::uint32_t;
    struct Endgame { Gaps wins, losses; };
    unsigned initial_parity = 0;
    std::vector<Endgame> endgame;
    unsigned low_count = 0;
    Word low_mask = 0;

    static Gaps reverse_bits(Gaps x) {
#if defined(__clang__)
        return __builtin_bitreverse32(x);
#else
        x = ((x & 0x55555555u) << 1) | ((x >> 1) & 0x55555555u);
        x = ((x & 0x33333333u) << 2) | ((x >> 2) & 0x33333333u);
        x = ((x & 0x0f0f0f0fu) << 4) | ((x >> 4) & 0x0f0f0f0fu);
        return __builtin_bswap32(x);
#endif
    }

    void build_endgame(int count) {
        if (!count || weights.empty()) return;
        if (weights.back() > 62) throw std::runtime_error("packed suffix tables require weights <= 62");
        count = std::min(count, static_cast<int>(weights.size()));
        low_count = weights.size() - count;
        low_mask = (Word{1} << low_count) - 1;
        for (int x : weights) initial_parity ^= x & 1;
        Word odd_tokens = 0;
        for (int i = 0; i < count; ++i)
            odd_tokens |= Word(weights[low_count+i] & 1) << i;

        endgame.resize(Word{1} << count);
        endgame[0] = {0, initial_parity ? ~Gaps{0} : ~Gaps{1}};
        for (Word mask = 1; mask < endgame.size(); ++mask) {
            const unsigned parity = initial_parity ^ __builtin_parityll(mask & odd_tokens);
            Endgame best{0, ~Gaps{0}};
            for (Word moves = mask; moves; moves &= moves - 1) {
                const Word bit = moves & -moves;
                const unsigned x = weights[low_count + __builtin_ctzll(bit)];
                const unsigned c = parity ^ (x & 1);
                const unsigned shift = (x+c)/2;
                const Gaps positive = ~Gaps{1} | c;
                const Endgame &child = endgame[mask ^ bit];
                // Child bit j represents deficit 2*j+c. In the continuing case
                // its parent bit is j+(x+c)/2. The passed case reflects about
                // floor((x-c)/2), including a zero child deficit.
                Gaps win = (child.wins & positive) << shift;
                Gaps loss = (child.losses & positive) << shift;
                if (x >= c) {
                    const unsigned right = 31-(x-c)/2;
                    win |= reverse_bits(child.losses) >> right;
                    loss |= reverse_bits(child.wins) >> right;
                }
                best.wins |= win;
                best.losses &= loss;
            }
            endgame[mask] = best;
        }
    }

    static int high(Word mask) { return 63 - __builtin_clzll(mask); }
    static Word hash(Word key) {
        key ^= key >> 30;
        key *= UINT64_C(0xbf58476d1ce4e5b9);
        key ^= key >> 27;
        return key * UINT64_C(0x94d049bb133111eb) ^ (key >> 31);
    }

public:
    Solver(std::vector<int> w, int cache_bits, bool small, int end_count, int starting_gap = 0)
        : weights(std::move(w)), cache(Word{1} << cache_bits), small_first(small) {
        const int bound = weights.empty() ? starting_gap : std::max(weights.back(), starting_gap);
        while ((Word{1} << gap_bits) <= static_cast<Word>(bound)) ++gap_bits;
        initial_parity = starting_gap & 1;
        if (end_count && starting_gap > 62) throw std::runtime_error("packed suffix tables require deficit <= 62");
        if (weights.size() + gap_bits + 2 > 64)
            throw std::runtime_error("weights and subset mask exceed the 64-bit cache key");
        build_endgame(end_count);
    }

    // strict = false asks whether the mover can avoid a loss; true asks for a win.
    bool reaches(Word mask, int gap, std::int64_t sum, bool strict) {
        if (sum <= gap) return sum == gap && !strict;
        if (2LL * weights[high(mask)] >= sum + gap + strict) return true;

        if (!endgame.empty() && !(mask & low_mask) && ((sum + gap) & 1) == initial_parity) {
            const auto &row = endgame[mask >> low_count];
            const Gaps bit = Gaps{1} << (gap/2);
            return strict ? (row.wins & bit) != 0 : (row.losses & bit) == 0;
        }
        const Word key = (((mask << gap_bits) | gap) << 1) | strict;
        Word &entry = cache[hash(key) & (cache.size() - 1)];
        if ((entry >> 1) == key) return (entry & 1) != 0;

        Word moves = mask;
        if (strict && gap == 0 && (mask & (mask-1))) {
            // A non-losing opening excludes a strict win from every other opening.
            const int i = small_first ? __builtin_ctzll(mask) : high(mask);
            const Word bit = Word{1} << i, rest = mask ^ bit;
            const int x = weights[i];
            if (!reaches(rest, x, sum-x, true)) {
                const bool won = !reaches(rest, x, sum-x, false);
                entry = (key << 1) | won;
                return won;
            }
            moves ^= bit; // This opening loses against a strict winning reply.
        }
        bool success = false;
        while (moves) {
            const int i = small_first ? __builtin_ctzll(moves) : high(moves);
            const Word bit = Word{1} << i;
            moves ^= bit;
            const int x = weights[i];
            if (x < gap)
                success = reaches(mask ^ bit, gap - x, sum - x, strict);
            else
                success = !reaches(mask ^ bit, x - gap, sum - x, !strict);
            if (success) break;
        }
        entry = (key << 1) | success;
        return success;
    }

    char value_at(Word mask, int d, std::int64_t sum) {
        if (reaches(mask, d, sum, true)) return 'W';
        return reaches(mask, d, sum, false) ? 'D' : 'L';
    }

    // The opening reversal theorem allows a tied board to be discharged by
    // checking two non-losing openings. Failure of that sufficient condition
    // falls back to both unrestricted minimax thresholds.
    char tied_value(Word mask, std::int64_t sum) {
        int holds = 0;
        Word moves = mask;
        for (int i = 0; i < 2 && moves; ++i, moves &= moves-1) {
            const Word bit = moves & -moves;
            const int x = weights[__builtin_ctzll(bit)];
            if (!reaches(mask ^ bit, x, sum-x, true)) ++holds;
        }
        return holds == 2 ? 'D' : value_at(mask, 0, sum);
    }

    void anchor_tests() {
        const int n = weights.size();
        const auto sum = std::int64_t{n} * (n+1) / 2;
        if (n < 3 || sum % 2) throw std::runtime_error("anchor tests need an even-total prefix, N >= 3");
        const Word full = (Word{1} << n)-1;
        const auto token = [](int x) { return Word{1} << (x-1); };
        std::cout << n;
        for (int a : {1, 2}) {
            std::array<int, 3> counts{};
            for (int b = a+1; b <= n; ++b) {
                if (b == 2*a) continue;
                const Word rest = full ^ token(a) ^ token(b) ^ token(b-a);
                const char v = tied_value(rest, sum-2*b);
                ++counts[v == 'W' ? 0 : v == 'D' ? 1 : 2];
            }
            for (int c : counts) std::cout << '\t' << c;
        }
        std::cout << '\t' << value_at(full ^ token(1) ^ token(2), 1, sum-3) << '\t';
        if (n >= 4) std::cout << value_at(full ^ token(2) ^ token(4), 2, sum-6);
        else std::cout << '-';
        std::cout << std::endl;
    }

    void all_roots() {
        if (weights.size() > 22) throw std::runtime_error("root census limited to 22 tokens");
        const Word limit = Word{1} << weights.size();
        std::vector<std::int64_t> sums(limit);
        for (Word mask = 0; mask < limit; ++mask) {
            if (mask) sums[mask] = sums[mask & (mask-1)] + weights[__builtin_ctzll(mask)];
            const bool win = reaches(mask, 0, sums[mask], true);
            const char value = win ? 'W' : reaches(mask, 0, sums[mask], false) ? 'D' : 'L';
            std::cout << value;
        }
        std::cout << '\n';
    }

    // Query many tied subboards of the same universe, sharing exact cache entries.
    void read_masks() {
        const Word full = (Word{1} << weights.size())-1;
        Word mask;
        while (std::cin >> mask) {
            if (mask & ~full) throw std::runtime_error("mask outside the specified universe");
            std::int64_t sum = 0;
            for (Word moves = mask; moves; moves &= moves-1)
                sum += weights[__builtin_ctzll(moves)];
            std::cout << mask << '\t' << tied_value(mask, sum) << '\n';
        }
        if (!std::cin.eof()) throw std::runtime_error("expected decimal subset masks");
    }

    void position(int d) {
        const Word mask = (Word{1} << weights.size())-1;
        const auto sum = std::accumulate(weights.begin(), weights.end(), std::int64_t{0});
        std::cout << weights.size() << '\t' << sum << '\t' << d << '\t'
                  << value_at(mask, d, sum) << std::endl;
    }

    void first_two() {
        if (weights.size() < 2) throw std::runtime_error("two openings required");
        const Word mask = (Word{1} << weights.size()) - 1;
        const auto sum = std::accumulate(weights.begin(), weights.end(), std::int64_t{0});
        for (int i = 0; i < 2; ++i) {
            const int x = weights[i];
            const bool holds = !reaches(mask ^ (Word{1} << i), x, sum - x, true);
            std::cout << weights.size() << '\t' << x << '\t' << (holds ? "holds" : "fails") << std::endl;
        }
    }

    void report() {
        const Word mask = (Word{1} << weights.size()) - 1;
        const auto sum = std::accumulate(weights.begin(), weights.end(), std::int64_t{0});
        std::string openings;
        for (std::size_t i = 0; i < weights.size(); ++i) {
            const Word rest = mask ^ (Word{1} << i);
            const int x = weights[i];
            // A forced first pick swaps players even at equality.
            const bool opponent_can_win = reaches(rest, x, sum - x, true);
            const bool opponent_can_hold = opponent_can_win || reaches(rest, x, sum - x, false);
            openings += opponent_can_win ? 'L' : opponent_can_hold ? 'D' : 'W';
        }
        const char value = openings.find('W') != std::string::npos ? 'W' :
                           openings.empty() || openings.find('D') != std::string::npos ? 'D' : 'L';
        std::cout << weights.size() << '\t' << sum << '\t' << value << '\t' << openings << std::endl;
    }
};

int main(int argc, char **argv) {
    try {
        bool small = false, custom = false, two = false, roots = false, anchors = false, masks = false;
        int cache_bits = 22, end_count = 0, starting_gap = -1;
        std::vector<int> args;
        for (int i = 1; i < argc; ++i) {
            const std::string arg = argv[i];
            if (arg == "--small-first") small = true;
            else if (arg == "--set") custom = true;
            else if (arg == "--gap" && i+1 < argc) {
                starting_gap = std::stoi(argv[++i]);
                if (starting_gap < 0) throw std::runtime_error("a deficit must be nonnegative");
            }
            else if (arg == "--anchors") anchors = true;
            else if (arg == "--roots") roots = true;
            else if (arg == "--masks") masks = true;
            else if (arg == "--two") two = true;
            else if (arg == "--endgame" && i + 1 < argc) end_count = std::stoi(argv[++i]);
            else if (arg == "--cache-bits" && i + 1 < argc) cache_bits = std::stoi(argv[++i]);
            else args.push_back(std::stoi(arg));
        }
        if (end_count < 0 || end_count > 28) throw std::runtime_error("endgame size must be 0..28");
        if (cache_bits < 0 || cache_bits > 28) throw std::runtime_error("cache bits must be 0..28");
        for (int x : args) if (x < 0) throw std::runtime_error("nonnegative inputs required");
        if (custom && anchors) throw std::runtime_error("anchor tests use consecutive prefixes");
        if (masks && !custom && args.size() != 1) throw std::runtime_error("mask input requires one universe");
        if (custom) {
            std::sort(args.begin(), args.end());
            if (std::adjacent_find(args.begin(), args.end()) != args.end())
                throw std::runtime_error("a set must contain distinct weights");
            Solver solver(args, cache_bits, small, end_count, std::max(0, starting_gap));
            if (starting_gap >= 0) solver.position(starting_gap);
            else if (masks) solver.read_masks();
            else if (roots) solver.all_roots();
            else if (two) solver.first_two();
            else solver.report();
        } else {
            if (args.empty()) throw std::runtime_error("supply prefix sizes, or --set followed by weights");
            for (int n : args) {
                if (n > 63) throw std::runtime_error("prefix too large for subset mask");
                std::vector<int> weights(n);
                std::iota(weights.begin(), weights.end(), 1);
                Solver solver(weights, cache_bits, small, end_count, std::max(0, starting_gap));
                if (starting_gap >= 0) solver.position(starting_gap);
                else if (masks) solver.read_masks();
                else if (anchors) solver.anchor_tests();
                else if (roots) solver.all_roots();
                else if (two) solver.first_two();
                else solver.report();
            }
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
