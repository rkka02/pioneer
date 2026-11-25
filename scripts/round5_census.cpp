// Vertex augmentation through minimum-degree deletions. A missing shape or a
// certified strong induced subgraph removes all of its possible target descendants.
#include <nauty/nauty.h>
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
using U = uint32_t;
using Word = uint64_t;
constexpr int CAPACITY = 16;
struct Graph {
    array<U, CAPACITY> row{};
};
struct Key {
    Word lo = 0, hi = 0;
    bool operator==(const Key &b) const { return lo == b.lo && hi == b.hi; }
};
struct Hash {
    size_t operator()(Key k) const {
        return k.lo ^ ((k.hi + 0x9e3779b97f4a7c15ULL) * 0xbf58476d1ce4e5b9ULL);
    }
};
static int pc(U s) { return __builtin_popcount(s); }
static int first(U s) { return __builtin_ctz(s); }
static U vbit(int i) { return 1u << i; }

static Key key_of(const Graph &g, int n) {
    Key out;
    for (int j = 1, i = 0; j < n; ++j)
        for (int k = 0; k < j; ++k, ++i)
            if (g.row[j] & vbit(k))
                (i < 64 ? out.lo : out.hi) |= Word(1) << (i % 64);
    return out;
}
static Graph decode(Key x, int n) {
    Graph g;
    for (int j = 1, i = 0; j < n; ++j)
        for (int k = 0; k < j; ++k, ++i)
            if (((i < 64 ? x.lo : x.hi) >> (i % 64)) & 1) {
                g.row[j] |= vbit(k);
                g.row[k] |= vbit(j);
            }
    return g;
}
static Key canonical(const Graph &g, int n) {
    graph a[CAPACITY] = {}, b[CAPACITY] = {};
    int lab[CAPACITY], ptn[CAPACITY], orbits[CAPACITY];
    DEFAULTOPTIONS_GRAPH(opt);
    opt.getcanon = TRUE;
    statsblk stats;
    for (int j = 0; j < n; ++j)
        for (U s = g.row[j]; s; s &= s - 1)
            ADDELEMENT(&a[j], first(s));
    densenauty(a, lab, ptn, orbits, &opt, &stats, 1, n, b);
    Graph c;
    for (int j = 0; j < n; ++j)
        for (int k = 0; k < n; ++k)
            if (ISELEMENT(&b[j], k))
                c.row[j] |= vbit(k);
    return key_of(c, n);
}
static int shape(const Graph &g, int n) {
    int code = 0;
    for (int i = 0; i < n; ++i)
        code += 1 << (4 * pc(g.row[i]));
    return code;
}
// An actual W4 through any center. Endpoints of its diagonals have two common rim neighbors.
static bool has_wheel(const Graph &g, int n) {
    for (int v = 0; v < n; ++v) {
        U rim = g.row[v];
        if (pc(rim) < 4)
            continue;
        for (U i = rim; i; i &= i - 1)
            for (U j = i & (i - 1); j; j &= j - 1)
                if (pc(g.row[first(i)] & g.row[first(j)] & rim) >= 2)
                    return true;
    }
    return false;
}
// Any tree of two or three disjoint K4s with triple matchings is strong
// after one additional interblock edge. At order at most 15 this covers all such trees.
static bool repaired_tree(const Graph &g, int n) {
    if (n < 8)
        return false;
    vector<U> cliques;
    for (int a = 0; a < n; ++a)
        for (U bs = g.row[a] & ~(vbit(a + 1) - 1); bs; bs &= bs - 1) {
            int b = first(bs);
            U both = g.row[a] & g.row[b] & ~(vbit(b + 1) - 1);
            for (U cs = both; cs; cs &= cs - 1) {
                int c = first(cs);
                for (U ds = (cs & (cs - 1)) & g.row[c]; ds; ds &= ds - 1)
                    cliques.push_back(vbit(a) | vbit(b) | vbit(c) | vbit(first(ds)));
            }
        }
    if (cliques.size() < 2)
        return false;
    auto interface = [&](U left, U right) {
        int count = 0;
        bool matching = false;
        for (U x = left; x; x &= x - 1) {
            U a = g.row[first(x)] & right;
            count += pc(a);
            for (U y = x & (x - 1); y; y &= y - 1) {
                U b = g.row[first(y)] & right;
                for (U z = y & (y - 1); z; z &= z - 1) {
                    U c = g.row[first(z)] & right;
                    if (a && b && c && pc(a | b) >= 2 && pc(a | c) >= 2 && pc(b | c) >= 2 &&
                        pc(a | b | c) >= 3)
                        matching = true;
                }
            }
        }
        return pair<int, bool>(count, matching);
    };
    for (size_t i = 0; i < cliques.size(); ++i)
        for (size_t j = i + 1; j < cliques.size(); ++j) {
            if (cliques[i] & cliques[j])
                continue;
            auto ij = interface(cliques[i], cliques[j]);
            if (ij.first >= 4 && ij.second)
                return true;
            for (size_t k = j + 1; k < cliques.size(); ++k) {
                if ((cliques[i] | cliques[j]) & cliques[k])
                    continue;
                auto ik = interface(cliques[i], cliques[k]), jk = interface(cliques[j], cliques[k]);
                if (int(ij.second) + ik.second + jk.second >= 2 && ij.first + ik.first + jk.first >= 7)
                    return true;
            }
        }
    return false;
}
// F3 vector addition on two bit planes, low for +1 and high for -1.
static U add(U x, U y) {
    U p = x & 65535, m = x >> 16, q = y & 65535, r = y >> 16;
    U a = ~(p | m), b = ~(q | r);
    return ((a & q) | (p & b) | (m & r)) | (((a & r) | (m & b) | (p & q)) << 16);
}
static U neg(U x) { return (x >> 16) | (x << 16); }
struct Holes {
    vector<U> list;
    unordered_set<U> set;
    bool contains(U x) const { return set.count(x) != 0; }
};
// Independent dense boundary DP on n-1 ternary coordinates; the final coordinate
// follows from conservation. Each edge updates disjoint cyclic orbits of length 3.
static Holes boundary_holes(const Graph &g, int n) {
    int pow3[CAPACITY + 1] = {1};
    for (int i = 0; i < n; ++i)
        pow3[i + 1] = 3 * pow3[i];
    int size = pow3[n - 1];
    vector<uint8_t> state(size);
    state[0] = 1;
    for (int a = 0; a < n; ++a)
        for (int b = a + 1; b < n; ++b)
            if (g.row[a] & vbit(b)) {
                int sa = pow3[a], sb = pow3[b];
                for (int block = 0; block < size; block += 3 * sb)
                    for (int j = 0; j < sb; j += 3 * sa)
                        for (int i = 0; i < sa; ++i)
                            for (int t = 0; t < (b == n - 1 ? 1 : 3); ++t) {
                                int root = block + j + i;
                                int u = root + (b == n - 1 ? 0 : t * sb);
                                int v = root + sa + (b == n - 1 ? 0 : ((t + 2) % 3) * sb);
                                int w = root + 2 * sa + (b == n - 1 ? 0 : ((t + 1) % 3) * sb);
                                auto x = state[u], y = state[v], z = state[w];
                                state[u] = y | z;
                                state[v] = x | z;
                                state[w] = x | y;
                            }
            }
    Holes out;
    for (int t = 0; t < size; ++t)
        if (!state[t]) {
            int a = t, sum = 0;
            U x = 0;
            for (int i = 0; i < n; ++i) {
                int s = i + 1 == n ? (3 - sum % 3) % 3 : a % 3;
                if (s)
                    x |= vbit(i + (s == 2 ? 16 : 0));
                sum += s;
                a /= 3;
            }
            out.list.push_back(x);
            out.set.insert(x);
        }
    return out;
}
// For a new star all possible demands at the leaf are allowed; test if, for one
// residue, a translate of every corresponding restriction lies in the parent holes.
static bool extension_has_hole(U neighbours, const Holes &parent) {
    array<vector<U>, 3> groups;
    for (U s = neighbours;; s = (s - 1) & neighbours) {
        int residue = (2 * pc(s) - pc(neighbours) + 18) % 3;
        groups[residue].push_back(s | ((neighbours ^ s) << 16));
        if (!s)
            break;
    }
    for (auto &states : groups) {
        if (states.empty())
            return true;
        U ref = states.front();
        for (U &entry : states)
            entry = add(ref, neg(entry));
        for (U h : parent.list) {
            bool all = true;
            for (size_t j = 1; j < states.size(); ++j)
                if (!parent.contains(add(h, states[j]))) {
                    all = false;
                    break;
                }
            if (all)
                return true;
        }
    }
    return false;
}
using Keys = unordered_set<Key, Hash>;
static unordered_set<int> valid[CAPACITY + 1];
static int hist_without(const Graph &g, int n, int v) {
    int s = 0;
    for (int i = 0; i < n; ++i)
        if (i != v)
            s += 1 << (4 * (pc(g.row[i]) - int((g.row[i] >> v) & 1)));
    return s;
}
static Graph omit(const Graph &g, int n, int v) {
    Graph f;
    U low = vbit(v) - 1;
    for (int i = 0; i < n; ++i)
        if (i != v)
            f.row[i - (i > v)] = (g.row[i] & low) | ((g.row[i] >> (v + 1)) << v);
    return f;
}
static void census(int target, int stop) {
    int n, h[6];
    while (cin >> n >> h[0] >> h[1] >> h[2] >> h[3] >> h[4] >> h[5]) {
        int code = 0;
        for (int k = 0; k < 6; ++k)
            code += h[k] << (4 * k);
        valid[n].insert(code);
    }
    Keys previous{Key{}};
    for (n = 2; n <= stop; ++n) {
        Keys next, seen;
        uint64_t wheel = 0, trees = 0, removed = 0, strong = 0, checked = 0;
        for (auto pk : previous) {
            Graph g = decode(pk, n - 1);
            U degrees[6] = {};
            for (int i = 0; i < n - 1; ++i)
                degrees[pc(g.row[i])] |= vbit(i);
            int base = shape(g, n - 1);
            vector<U> choices;
            for (U s = 0; s < vbit(n - 1); ++s) {
                int d = pc(s);
                if (d > 5 || (s & degrees[5]))
                    continue;
                int code = base + (1 << (4 * d));
                bool good = true;
                for (int i = 0; i < 5; ++i) {
                    U inc = s & degrees[i];
                    if ((i < d && (degrees[i] & ~s)) || (i + 1 < d && inc)) {
                        good = false;
                        break;
                    }
                    code += 15 * pc(inc) * (1 << (4 * i));
                }
                if (good && valid[n].count(code))
                    choices.push_back(s);
            }
            if (choices.empty())
                continue;
            Holes holes;
            bool loaded = false;
            for (U s : choices) {
                Graph f = g;
                f.row[n - 1] = s;
                for (U t = s; t; t &= t - 1)
                    f.row[first(t)] |= vbit(n - 1);
                Key k = canonical(f, n);
                if (!seen.insert(k).second)
                    continue;
                ++checked;
                if (has_wheel(f, n)) {
                    ++wheel;
                    continue;
                }
                if (repaired_tree(f, n)) {
                    ++trees;
                    continue;
                }
                bool reject = false;
                for (int v = 0; v < n - 1; ++v)
                    if (valid[n - 1].count(hist_without(f, n, v))) {
                        if (!previous.count(canonical(omit(f, n, v), n - 1))) {
                            reject = true;
                            break;
                        }
                    }
                if (reject) {
                    ++removed;
                    continue;
                }
                if (pc(s) >= 2) {
                    if (!loaded) {
                        holes = boundary_holes(g, n - 1);
                        loaded = true;
                    }
                    if (!extension_has_hole(s, holes)) {
                        ++strong;
                        continue;
                    }
                }
                next.insert(k);
            }
        }
        if (checked != wheel + trees + removed + strong + next.size())
            throw runtime_error("class counts");
        cout << target << " " << n << " " << previous.size() << " " << checked << " " << wheel << " "
             << trees << " " << removed << " " << strong << " " << next.size() << endl;
        if (n == target)
            for (Key k : next)
                cout << "survivor " << n << " " << k.lo << " " << k.hi << endl;
        previous = std::move(next);
    }
}
int main(int argc, char **argv) {
    if (argc == 2 && string(argv[1]) == "--probe") {
        int n;
        Word mask;
        U neighbors;
        while (cin >> n >> mask >> neighbors) {
            if (n < 1 || n > 8 || neighbors >= vbit(n))
                return 2;
            Graph g = decode({mask, 0}, n);
            Holes holes = boundary_holes(g, n);
            cout << holes.list.size() << " " << extension_has_hole(neighbors, holes) << "\n";
        }
        return 0;
    }
    if (argc != 3 || atoi(argv[1]) < 5 || atoi(argv[1]) > 15 || atoi(argv[2]) < 2 ||
        atoi(argv[2]) > atoi(argv[1]))
        return 2;
    census(atoi(argv[1]), atoi(argv[2]));
}
