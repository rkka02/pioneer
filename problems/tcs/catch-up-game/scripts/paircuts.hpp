#pragma once
#include <cstdint>

namespace catchup {

// For unit-spaced bit positions, the number of sites with an odd number of
// tokens at or below them is the sum of the sorted adjacent-pair differences.
inline int spread(std::uint64_t even_board) {
    even_board ^= even_board << 1;
    even_board ^= even_board << 2;
    even_board ^= even_board << 4;
    even_board ^= even_board << 8;
    even_board ^= even_board << 16;
    even_board ^= even_board << 32;
    return __builtin_popcountll(even_board);
}

// -1 gives no bound, 0 excludes a mover win, and 1 forces a mover loss.
// The least token has value base plus its zero-based bit index.
inline int pair_bound(std::uint64_t board, int base, int gap) {
    std::int64_t bank = 0;
    int best = -1;
    int count = __builtin_popcountll(board);
    while (board && bank + count/2 <= gap) {
        const std::int64_t low = std::int64_t(base) + __builtin_ctzll(board);
        if ((count & 1) == 0) {
            const auto second = std::int64_t(base) + __builtin_ctzll(board & (board-1));
            if (second >= std::int64_t(gap) + count/2) {
                const int e = spread(board);
                if (second >= std::int64_t(gap) + e && bank + e <= gap) {
                    if (bank + e < gap) return 1;
                    best = 0;
                }
            }
        }
        bank += low;
        board &= board - 1;
        --count;
    }
    return best;
}

}
