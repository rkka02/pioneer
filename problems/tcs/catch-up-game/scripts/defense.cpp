// Check whether an opener can reach half the total against every reply.
// Below the chosen suffix, the defender may take one of the k smallest live
// tokens. The opponent is unrestricted. A successful restricted search is a proof.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Mask = std::uint64_t;
using Gaps = std::uint32_t;
struct MemoRow { std::array<Gaps, 2> known{}, hold{}; };
struct GoalRow { Gaps defender, opponent; };

class Defense {
    int n, free_count, choices, half;
    bool endpoints;
    Mask low_mask;
    std::vector<MemoRow> suffix;
    std::vector<GoalRow> complete;
    std::vector<Mask> cache;

    void build_suffix() {
        // Fixed defender, fixed half-total goal. Lower deficits run from right to left
        // in the defender word (bit 31 is the smallest) and left to right in the
        // opponent word (bit 0 is the smallest). Passing then needs no bit reversal.
        const int base = n-free_count;
        Mask odd_tokens = 0;
        for (int i = 0; i < free_count; ++i)
            if ((base+i+1) % 2) odd_tokens |= Mask{1} << i;
        complete.resize(Mask{1} << free_count);
        complete[0] = {Gaps{1} << 31, ~Gaps{0}};
        for (Mask board = 1; board < complete.size(); ++board) {
            const unsigned parity = __builtin_parityll(board & odd_tokens);
            GoalRow best{0, ~Gaps{0}};
            for (Mask moves = board; moves; moves &= moves-1) {
                const Mask bit = moves & -moves;
                const unsigned x = base + __builtin_ctzll(bit) + 1;
                const unsigned c = parity ^ (x & 1), shift = (x+c)/2, cross = 31-(x-c)/2;
                const GoalRow &child = complete[board ^ bit];
                const Gaps same_defender = c ? child.defender : child.defender & ~(Gaps{1} << 31);
                const Gaps same_opponent = c ? child.opponent : child.opponent & ~Gaps{1};
                best.defender |= (same_defender >> shift) | (child.opponent << cross);
                best.opponent &= (same_opponent << shift) | (child.defender >> cross);
            }
            complete[board] = best;
        }
    }

    bool play(Mask board, int mine, int theirs, bool my_turn) {
        if (mine >= half || theirs == half) return true;
        if (theirs > half) return false;
        // Board nonempty here, since both scores are strictly below half.
        const bool free = (board & low_mask) == 0;
        const int gap = my_turn ? theirs - mine : mine - theirs;
        if (free && !complete.empty()) {
            const GoalRow &row = complete[board >> (n-free_count)];
            const unsigned k = gap/2;
            return my_turn ? (row.defender >> (31-k)) & 1 : (row.opponent >> k) & 1;
        }
        const int largest = 64-__builtin_clzll(board);
        if (!my_turn && theirs+largest > half) return false;
        if (my_turn && (free || choices >= n || endpoints) && mine+largest >= half) return true;
        // For a fixed board, gap and the sum already taken have the same parity.
        const std::uint32_t bit_gap = std::uint32_t{1} << (gap / 2);
        const Mask key = ((board * (half + 1) + mine) << 1) | my_turn;
        const Mask mixed = (key ^ (key >> 23)) * UINT64_C(0x9e3779b97f4a7c15);
        Mask &slot = cache[(mixed ^ (mixed >> 31)) & (cache.size() - 1)];
        if (free) {
            const MemoRow &row = suffix[board >> (n - free_count)];
            if (row.known[my_turn] & bit_gap) return (row.hold[my_turn] & bit_gap) != 0;
        } else if ((slot >> 1) == key) {
            return slot & 1;
        }

        bool holds = !my_turn; // existential defender, universal opponent
        Mask options = board;
        if (my_turn && !free && choices < n) {
            Mask above_low = board, below_high = board;
            for (int i = 0; i < choices && above_low; ++i) {
                above_low &= above_low - 1;
                if (endpoints) below_high ^= Mask{1} << (63 - __builtin_clzll(below_high));
            }
            options &= ~(above_low & below_high);
        }
        for (Mask moves = options; moves; moves &= moves - 1) {
            const Mask bit = moves & -moves;
            const int x = __builtin_ctzll(bit) + 1;
            if (my_turn)
                holds = play(board ^ bit, mine + x, theirs, mine + x < theirs);
            else
                holds = play(board ^ bit, mine, theirs + x, theirs + x >= mine);
            if (holds == my_turn) break;
        }
        if (free) {
            MemoRow &row = suffix[board >> (n - free_count)];
            row.known[my_turn] |= bit_gap;
            if (holds) row.hold[my_turn] |= bit_gap;
        } else {
            slot = (key << 1) | holds;
        }
        return holds;
    }

public:
    Defense(int size, int suffix_size, int k, bool ends, bool packed)
        : n(size), free_count(suffix_size), choices(k), half(n * (n + 1) / 4),
          endpoints(ends), low_mask((Mask{1} << (n - free_count)) - 1), suffix(packed ? 0 : Mask{1} << free_count),
          cache(Mask{1} << (n >= 39 ? 25 : 23)) {
        if (packed) build_suffix();
    }
    bool second_holds(int a, int b) {
        const Mask remaining = ((Mask{1} << n)-1) ^ (Mask{1} << (a-1)) ^ (Mask{1} << (b-1));
        return play(remaining, b, a, b < a);
    }

    bool opening(int x) {
        return play(((Mask{1} << n) - 1) ^ (Mask{1} << (x - 1)), x, 0, false);
    }
};

int main(int argc, char **argv) {
    try {
        if (argc < 5) throw std::runtime_error("usage: defense N free_top_count choices [--ends] [--packed] opening ... (or --reply a b)");
        int n = std::stoi(argv[1]), free_count = std::stoi(argv[2]), k = std::stoi(argv[3]);
        // At N=52 the board, score and two Boolean flags still fit a 64-bit key.
        if (n < 1 || n > 52 || (n * (n + 1) / 2) % 2 || free_count < 0 ||
            free_count > std::min(n, 28) || k < 1)
            throw std::runtime_error("need even total, N=1..52, suffix size 0..min(N,28), choices >=1");
        bool ends = false, packed = false, reply = false;
        int first = 4;
        while (first < argc) {
            const std::string option = argv[first];
            if (option == "--ends") ends = true;
            else if (option == "--packed") packed = true;
            else if (option == "--reply") reply = true;
            else break;
            ++first;
        }
        if (first == argc) throw std::runtime_error("supply an opening");
        Defense verifier(n, free_count, k, ends, packed);
        if (reply) {
            if (argc-first != 2) throw std::runtime_error("a conditional reply needs two distinct picks");
            const int a = std::stoi(argv[first]), b = std::stoi(argv[first+1]);
            if (a < 1 || a > n || b < 1 || b > n || a == b) throw std::runtime_error("invalid pair");
            std::cout << n << '\t' << a << '\t' << b << '\t'
                      << (verifier.second_holds(a,b) ? "P2 holds" : "P2 fails") << std::endl;
            return 0;
        }
        for (int i = first; i < argc; ++i) {
            const int x = std::stoi(argv[i]);
            if (x < 1 || x > n) throw std::runtime_error("opening outside board");
            std::cout << n << '\t' << free_count << '\t' << k << '\t' << x << '\t'
                      << (verifier.opening(x) ? "holds" : "fails") << std::endl;
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
