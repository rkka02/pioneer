// All five-token order types have a positive integral representative with maximum <= 55.
// The determinant argument is in RESEARCH_ANALYSIS.md. Compare every opening margin
// from a closed endgame formula with a separate full game tree in absolute scores.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>

using Board = std::array<int, 5>;

static int pair_margin(int u, int v, int gap) {
    return gap <= u ? v-u-gap : u+v-gap;
}

static int triple_margin(const std::array<int, 3> &r, int gap) {
    auto move = [gap](int x, int u, int v) {
        return x < gap ? pair_margin(u, v, gap-x) : -pair_margin(u, v, x-gap);
    };
    return std::max({move(r[0], r[1], r[2]), move(r[1], r[0], r[2]), move(r[2], r[0], r[1])});
}

static Board opening_rows(const Board &s) {
    Board rows;
    rows.fill(std::numeric_limits<int>::max());
    for (int a = 0; a < 5; ++a) {
        for (int b = a+1; b < 5; ++b) {
            std::array<int, 3> rest{};
            int k = 0;
            for (int i = 0; i < 5; ++i) {
                if (i != a && i != b) rest[k++] = s[i];
            }
            const int margin = triple_margin(rest, s[b]-s[a]);
            rows[a] = std::min(rows[a], margin);
            rows[b] = std::min(rows[b], -margin);
        }
    }
    return rows;
}

static int absolute_tree(const Board &s, unsigned mask, int p1, int p2, bool first_acts) {
    if (!mask) return p1-p2;
    int best = first_acts ? std::numeric_limits<int>::min() : std::numeric_limits<int>::max();
    for (unsigned moves = mask; moves; moves &= moves-1) {
        const unsigned bit = moves & -moves;
        const int x = s[__builtin_ctz(bit)];
        if (first_acts)
            best = std::max(best, absolute_tree(s, mask ^ bit, p1+x, p2, p1+x < p2));
        else
            best = std::min(best, absolute_tree(s, mask ^ bit, p1, p2+x, p2+x >= p1));
    }
    return best;
}

int main() {
    std::uint64_t boards = 0, wins = 0, draws = 0, losses = 0, draws_with_two = 0;
    for (int e = 5; e <= 55; ++e)
    for (int d = 4; d < e; ++d)
    for (int c = 3; c < d; ++c)
    for (int b = 2; b < c; ++b)
    for (int a = 1; a < b; ++a) {
        const Board s{a,b,c,d,e};
        const Board rows = opening_rows(s);
        for (int i = 0; i < 5; ++i) {
            const int other = absolute_tree(s, 31u ^ (1u << i), s[i], 0, false);
            if (rows[i] != other) {
                std::cerr << "Opening margin mismatch on";
                for (int x : s) std::cerr << ' ' << x;
                std::cerr << " at opening " << s[i] << '\n';
                return 1;
            }
        }
        ++boards;
        const int root = *std::max_element(rows.begin(), rows.end());
        if (root > 0) ++wins;
        else if (root < 0) ++losses;
        else {
            ++draws;
            if (std::count(rows.begin(), rows.end(), 0) == 2) ++draws_with_two;
        }
    }
    std::cout << "boards " << boards << ", opening margins compared " << 5*boards
              << ", wins " << wins << ", draws " << draws << ", losses " << losses
              << ", draws with two drawing openings " << draws_with_two << '\n';
    return boards == 3478761 && losses == 0 && draws == draws_with_two ? 0 : 1;
}
