// Independent census: no nauty, with partition refinement and exhaustive
// individualization. Boundary reachability uses subset sums, packed in base three.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using Mask = uint16_t;
using Num = uint64_t;
constexpr int limit = 15;
int pop(unsigned x) { return __builtin_popcount(x); }
int indexOf(unsigned x) { return __builtin_ctz(x); }
struct Graph {
    array<Mask, limit> rows{};
    int n = 0;
};
using Code = unsigned __int128;
struct CodeHash {
    size_t operator()(Code k) const { return uint64_t(k) * 0x9e3779b97f4a7c15ull ^ uint64_t(k >> 64); }
};
using Classes = unordered_set<Code, CodeHash>;
struct CellList {
    array<Mask, limit> cell{};
    int count = 0;
};
static Code orderCode(const Graph &g, const CellList &p) {
    int perm[limit], size = 0;
    for (int j = 0; j < p.count; ++j)
        for (unsigned s = p.cell[j]; s; s &= s - 1)
            perm[size++] = indexOf(s);
    Code ans = 0;
    for (int j = 1; j < size; ++j)
        for (int i = 0; i < j; ++i)
            ans = (ans << 1) | ((g.rows[perm[i]] >> perm[j]) & 1u);
    return ans;
}
static bool twins(const Graph &g, unsigned cell) {
    int v = indexOf(cell);
    for (unsigned s = cell & (cell - 1); s; s &= s - 1) {
        int u = indexOf(s);
        if ((g.rows[u] ^ g.rows[v]) & ~((1u << u) | (1u << v)))
            return false;
    }
    return true;
}
static Code individualize(const Graph &g, CellList p) {
    // Every ordering decision is invariant under relabelling, except branches
    // over all choices. A cell of pairwise twins may use any internal order.
    while (true) {
        CellList q;
        for (int c = 0; c < p.count; ++c) {
            unsigned group = p.cell[c];
            if ((group & (group - 1)) == 0) {
                q.cell[q.count++] = group;
                continue;
            }
            array<pair<Num, int>, limit> signatures;
            int len = 0;
            for (unsigned s = group; s; s &= s - 1) {
                int v = indexOf(s);
                Num sig = 0;
                for (int k = 0; k < p.count; ++k)
                    sig = (sig << 3) | pop(g.rows[v] & p.cell[k]);
                signatures[len++] = {sig, v};
            }
            sort(signatures.begin(), signatures.begin() + len);
            for (int i = 0; i < len; ++i) {
                if (i == 0 || signatures[i].first != signatures[i - 1].first)
                    ++q.count;
                q.cell[q.count - 1] |= 1u << signatures[i].second;
            }
        }
        if (q.count == p.count)
            break;
        p = q;
    }
    int pick = -1, best = limit + 1;
    for (int c = 0; c < p.count; ++c) {
        int size = pop(p.cell[c]);
        if (size > 1 && size < best && !twins(g, p.cell[c])) {
            pick = c;
            best = size;
        }
    }
    if (pick < 0)
        return orderCode(g, p);
    Code result = ~Code(0);
    for (unsigned s = p.cell[pick]; s; s &= s - 1) {
        CellList q;
        for (int c = 0; c < p.count; ++c) {
            if (c == pick) {
                Mask one = s & -s;
                q.cell[q.count++] = one;
                q.cell[q.count++] = p.cell[c] ^ one;
            } else
                q.cell[q.count++] = p.cell[c];
        }
        result = min(result, individualize(g, q));
    }
    return result;
}
static Code normalize(const Graph &g) {
    CellList p;
    p.count = 1;
    p.cell[0] = (1u << g.n) - 1;
    return individualize(g, p);
}
static Graph unpack(Code code, int n) {
    Graph g;
    g.n = n;
    for (int j = n - 1; j > 0; --j)
        for (int i = j - 1; i >= 0; --i) {
            if (code & 1) {
                g.rows[i] |= 1u << j;
                g.rows[j] |= 1u << i;
            }
            code >>= 1;
        }
    return g;
}
static Num profile(const Graph &g, int skip = -1) {
    Num z = 0;
    for (int i = 0; i < g.n; ++i)
        if (i != skip) {
            int d = pop(g.rows[i]) - (skip < 0 ? 0 : (g.rows[i] >> skip) & 1u);
            z += Num(1) << (5 * d);
        }
    return z;
}
static Graph without(const Graph &g, int v) {
    Graph ans;
    ans.n = g.n - 1;
    for (int j = 0; j < g.n; ++j)
        if (j != v) {
            unsigned row = g.rows[j];
            ans.rows[j - (j > v)] = (row & ((1u << v) - 1)) | ((row >> (v + 1)) << v);
        }
    return ans;
}
static vector<unordered_set<Num>> profiles(int n) {
    vector<unordered_set<Num>> levels(n + 1);
    for (int d2 = 0; d2 <= 2; ++d2) {
        int d1 = 5 - 2 * d2;
        levels[n].insert((Num(d2) << 15) + (Num(d1) << 20) + (Num(n - d2 - d1) << 25));
    }
    for (int k = n; k > 1; --k)
        for (Num shape : levels[k]) {
            vector<int> d;
            for (int j = 0; j <= 5; ++j)
                for (unsigned i = 0; i < ((shape >> (5 * j)) & 31); ++i)
                    d.push_back(j);
            assert(int(d.size()) == k);
            for (unsigned s = 0; s < (1u << (k - 1)); ++s) {
                if (pop(s) != d[0])
                    continue;
                Num parent = 0;
                bool possible = true;
                for (int i = 1; i < k; ++i) {
                    int x = d[i] - ((s >> (i - 1)) & 1);
                    if (x < 0) {
                        possible = false;
                        break;
                    }
                    parent += Num(1) << (5 * x);
                }
                if (possible)
                    levels[k - 1].insert(parent);
            }
        }
    return levels;
}
static bool wheel(const Graph &g) {
    for (int v = 0; v < g.n; ++v) {
        unsigned ns = g.rows[v];
        if (pop(ns) < 4)
            continue;
        for (unsigned s = ns; s; s = (s - 1) & ns)
            if (pop(s) == 4) {
                bool yes = true;
                for (unsigned t = s; t; t &= t - 1)
                    if (pop(g.rows[indexOf(t)] & s) < 2) {
                        yes = false;
                        break;
                    }
                if (yes)
                    return true;
            }
    }
    return false;
}
static int powers[limit + 1], add81[81][81];
static unsigned lowerMove[3][2][3];
static void tables() {
    powers[0] = 1;
    for (int i = 1; i <= limit; ++i)
        powers[i] = powers[i - 1] * 3;
    for (int a = 0; a < 81; ++a)
        for (int b = 0; b < 81; ++b) {
            int c = 0;
            for (int s = 1; s < 81; s *= 3)
                c += s * ((a / s % 3 + b / s % 3) % 3);
            add81[a][b] = c;
        }
    for (int i = 0; i < 3; ++i)
        for (int x = 0; x < 27; ++x)
            for (int s = 0; s < 2; ++s)
                lowerMove[i][s][x / powers[i] % 3] |= 1u << x;
}
static unsigned shiftLow(unsigned bits, int i, int sign) {
    int step = powers[i];
    if (sign > 0)
        return ((bits & ~lowerMove[i][0][2]) << step) | ((bits & lowerMove[i][0][2]) >> (2 * step));
    return ((bits & ~lowerMove[i][1][0]) >> step) | ((bits & lowerMove[i][1][0]) << (2 * step));
}
static int shiftHigh(int word, int i, int sign) {
    int stride = powers[i - 3], digit = word / stride % 3;
    return word + stride * (sign == 1 ? (digit == 2 ? -2 : 1) : (digit == 0 ? 2 : -1));
}
struct Support {
    vector<unsigned> reached;
    vector<int> gap;
    Support(const Graph &g) {
        int dim = g.n - 1, size = powers[dim], words = (size + 26) / 27;
        reached.resize(words);
        reached[0] = 1;
        vector<unsigned> next(words);
        for (int j = 1; j < g.n; ++j)
            for (int i = 0; i < j; ++i)
                if ((g.rows[j] >> i) & 1) {
                    for (int w = 0; w < words; ++w) {
                        // Pull back the high ternary digits, push forward the bits in the low digits.
                        int from = w;
                        if (i >= 3)
                            from = shiftHigh(from, i, -1);
                        if (j >= 3 && j < dim)
                            from = shiftHigh(from, j, 1);
                        auto bits = reached[from];
                        if (i < 3)
                            bits = shiftLow(bits, i, 1);
                        if (j < 3 && j < dim)
                            bits = shiftLow(bits, j, -1);
                        next[w] = reached[w] | bits;
                    }
                    reached.swap(next);
                }
        for (int w = 0; w < words; ++w) {
            unsigned absent = ~reached[w] & ((1u << min(27, size - 27 * w)) - 1);
            for (; absent; absent &= absent - 1)
                gap.push_back(27 * w + indexOf(absent));
        }
    }
    bool hit(int x) const { return (reached[x / 27] >> (x % 27)) & 1; }
};
static int addIndex(int a, int b) {
    int v = add81[a % 81][b % 81] + 81 * add81[a / 81 % 81][b / 81 % 81];
    return v + 6561 * (add81[a / 6561 % 81][b / 6561 % 81] + 81 * add81[a / 531441][b / 531441]);
}
static bool missing(const Support &support, unsigned ns, int n) {
    // Signs {+1,-1} are an affine translate of subset sums {0,1}. For a fixed
    // total at the new vertex, an old hole must survive every allowable subset.
    vector<unsigned> choices[3];
    for (unsigned s = ns;; s = (s - 1) & ns) {
        choices[pop(s) % 3].push_back(s);
        if (!s)
            break;
    }
    for (const auto &bucket : choices) {
        if (bucket.empty())
            return true;
        vector<int> delta;
        for (size_t j = 1; j < bucket.size(); ++j) {
            int offset = 0;
            for (int i = 0; i < n - 1; ++i) {
                int side = (int((bucket[j] >> i) & 1) - int((bucket[0] >> i) & 1) + 3) % 3;
                offset += side * powers[i];
            }
            delta.push_back(offset);
        }
        for (int h : support.gap) {
            bool fails = true;
            for (int d : delta)
                if (support.hit(addIndex(h, d))) {
                    fails = false;
                    break;
                }
            if (fails)
                return true;
        }
    }
    return false;
}
int main(int argc, char **argv) {
    if (argc != 2)
        return 2;
    if (string(argv[1]) == "--probe") {
        tables();
        int n;
        Num mask;
        unsigned neighbors;
        while (cin >> n >> mask >> neighbors) {
            if (n < 1 || n > 8 || neighbors >= (1u << n))
                return 2;
            Graph g;
            g.n = n;
            for (int j = 1, bit = 0; j < n; ++j)
                for (int i = 0; i < j; ++i, ++bit)
                    if ((mask >> bit) & 1) {
                        g.rows[i] |= 1u << j;
                        g.rows[j] |= 1u << i;
                    }
            Support s(g);
            cout << s.gap.size() << " " << missing(s, neighbors, n) << "\n";
        }
        return 0;
    }
    int target = atoi(argv[1]);
    if (target < 5 || target > 15)
        return 2;
    tables();
    auto shape = profiles(target);
    Classes parents{0};
    for (int k = 2; k <= target; ++k) {
        Classes seen, next;
        uint64_t ancestry = 0, strong = 0, wheels = 0;
        for (auto key : parents) {
            Graph g = unpack(key, k - 1);
            unsigned banned = 0, must[6]{}, atLeast[6]{};
            for (int i = 0; i < g.n; ++i) {
                int d = pop(g.rows[i]);
                if (d == 5)
                    banned |= 1u << i;
                for (int j = 0; j <= 5; ++j) {
                    if (d < j)
                        must[j] |= 1u << i;
                    if (d + 1 < j)
                        atLeast[j] |= 1u << i;
                }
            }
            vector<unsigned> pending;
            unsigned available = ((1u << g.n) - 1) ^ banned;
            for (unsigned ns = available;; ns = (ns - 1) & available) {
                int d = pop(ns);
                if (d <= 5 && !atLeast[d] && !(must[d] & ~ns)) {
                    Graph child = g;
                    child.n = k;
                    child.rows[k - 1] = ns;
                    for (unsigned t = ns; t; t &= t - 1)
                        child.rows[indexOf(t)] |= 1u << (k - 1);
                    if (shape[k].count(profile(child))) {
                        Code iso = normalize(child);
                        if (seen.insert(iso).second) {
                            if (wheel(child))
                                ++wheels;
                            else {
                                bool possible = true;
                                for (int v = 0; v < g.n; ++v)
                                    if (shape[k - 1].count(profile(child, v)) &&
                                        !parents.count(normalize(without(child, v)))) {
                                        possible = false;
                                        break;
                                    }
                                if (!possible)
                                    ++ancestry;
                                else if (d < 2)
                                    next.insert(iso);
                                else
                                    pending.push_back(ns);
                            }
                        }
                    }
                }
                if (!ns)
                    break;
            }
            if (pending.empty())
                continue;
            Support support(g);
            for (unsigned ns : pending) {
                if (!missing(support, ns, g.n)) {
                    ++strong;
                    continue;
                }
                Graph keep = g;
                keep.rows[k - 1] = ns;
                keep.n = k;
                for (unsigned t = ns; t; t &= t - 1)
                    keep.rows[indexOf(t)] |= 1u << (k - 1);
                next.insert(normalize(keep));
            }
        }
        if (seen.size() != wheels + ancestry + strong + next.size())
            throw runtime_error("accounting");
        cout << target << " " << k << " " << parents.size() << " " << seen.size() << " " << wheels << " "
             << ancestry << " " << strong << " " << next.size() << endl;
        parents.swap(next);
    }
}
