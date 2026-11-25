// Unit-normalized ten-set census, with a checkpoint for every fourth coordinate.
#include "ten_search_core.hpp"

struct Normalization {
    const Modulus &m;
    int z;
    bool cover, fast;
    std::array<int, 1024> color{};
    std::vector<Bits> later, laterColor;
    // For sorted a<b, store all c>b whose triple has normalized third at least z.
    std::vector<Bits> triples;
    Normalization(const Modulus &mod, int third, bool useCover, bool fastMode = false)
        : m(mod), z(third), cover(useCover), fast(fastMode), later(m.n), laterColor(m.n),
          triples(m.n * (m.n - 1) / 2) {
        for (int x = 0; x < m.n; ++x)
            color[x] = ((137 * x) % m.n) % 3;
        if (cover)
            for (int x = 0; x < m.n; ++x)
                for (int y = 0; y < m.n; ++y) {
                    if (y > x)
                        m.set(later[x], y);
                    if (y > x || color[x] != color[y])
                        m.set(laterColor[x], y);
                }
        for (int a = 0; a < m.n; ++a)
            for (int b = a + 1; b < m.n; ++b) {
                Bits &row = triples[index(a, b)];
                for (int c = b + 1; c < m.n; ++c)
                    if (m.tripleMin[(b - a) * m.n + c - a] >= z && m.admissible[c - b] &&
                        m.admissible[b - a] && m.admissible[c - a]) {
                        m.set(row, c);
                        if (cover) {
                            m.set(triples[index(a, c)], b);
                            m.set(triples[index(b, c)], a);
                        }
                    }
            }
    }
    int index(int a, int b) const { return a * (2 * m.n - a - 1) / 2 + b - a - 1; }
    const Bits &after(int a, int b) const {
        return a < b ? triples[index(a, b)] : triples[index(b, a)];
    }
};

struct Statistics {
    std::uint64_t six = 0, covered = 0, sparse = 0, dense = 0, targets = 0, cliques = 0, valid = 0;
    void add(const Statistics &s) {
        six += s.six;
        covered += s.covered;
        sparse += s.sparse;
        dense += s.dense;
        targets += s.targets;
        cliques += s.cliques;
        valid += s.valid;
    }
};

template <class F> inline void eachBit(const Bits &bits, int words, F visit) {
    for (int w = 0; w < words; ++w) {
        Word v = bits[w];
        while (v) {
            int b = __builtin_ctzll(v);
            v &= v - 1;
            visit(64 * w + b);
        }
    }
}

struct CliqueSearch {
    const Normalization &normal;
    const Modulus &m;
    Points points{};
    Statistics stats{};
    std::vector<Points> leaves;
    // Pair buckets use timestamps so a tiny target graph costs no modulus-sized clear.
    std::array<int, 1024> head{}, stamp{};
    int epoch = 0;
    struct Edge {
        int first, second, next;
    };
    std::vector<Edge> pairs;
    std::array<std::vector<int>, 11> vertices;
    static constexpr int sparseLimit = 48;

    explicit CliqueSearch(const Normalization &norm) : normal(norm), m(norm.m) {}
    Bits nextMask(const Bits &prior, int k, int x) const {
        Bits result = prior;
        for (int i = 0; i < k; ++i) {
            const Bits &allowed = normal.after(points[i], x);
            for (int j = 0; j < m.words; ++j)
                result[j] &= allowed[j];
        }
        return result;
    }
    void trim(Bits &row, int last, bool sameColor) const {
        if (!normal.cover)
            return;
        const auto &allowed = sameColor ? normal.laterColor[last] : normal.later[last];
        for (int i = 0; i < m.words; ++i)
            row[i] &= allowed[i];
    }
    Bits holes(const Bits &row) const {
        Bits result{};
        for (int i = 0; i < m.words; ++i)
            result[i] = ~row[i];
        result[m.words - 1] &= m.last;
        return result;
    }
    int bits(const Bits &row) const {
        int n = 0;
        for (int j = 0; j < m.words; ++j)
            n += __builtin_popcountll(row[j]);
        return n;
    }
    bool vertex(const Rows &rows, int sigma, int x) const {
        int s = sigma;
        for (int h = 1; h <= 10; ++h) {
            s = m.sub(s, x);
            if (m.has(rows[10 - h], s))
                return false;
        }
        return true;
    }
    bool edge(const Rows &rows, int sigma, int x, int y) const {
        // The positive multiplicities of both new vertices are the only cases
        // not already checked for each separate vertex.
        int start = sigma;
        for (int h = 1; h < 10; ++h) {
            start = m.sub(start, x);
            int s = start;
            for (int j = 1; h + j <= 10; ++j) {
                s = m.sub(s, y);
                if (m.has(rows[10 - h - j], s))
                    return false;
            }
        }
        return true;
    }
    bool normalizedTail(int k) const {
        for (int j = k; j < 10; ++j)
            for (int b = 1; b < j; ++b)
                for (int a = 0; a < b; ++a)
                    if (!m.has(normal.after(points[a], points[b]), points[j]))
                        return false;
        return true;
    }
    void verify(int k) {
        if (!normalizedTail(k))
            return;
        ++stats.cliques;
        // Exact insertion after every coordinate avoids the expensive scalar
        // verifier for cliques containing a rival with three or four new values.
        Rows rows{};
        for (auto &r : rows)
            r[0] = 1;
        int sum = 0;
        for (int i = 1; i < 10; ++i) {
            if (!m.permits(rows, i, sum, points[i]))
                return;
            Rows updated{};
            m.adjoin(updated, rows, points[i]);
            rows = updated;
            sum = m.add(sum, points[i]);
        }
        if (!m.direct(points))
            throw std::logic_error("independent leaf check");
        ++stats.valid;
        leaves.push_back(points);
    }

    void targetGraph(const Rows &rows, int k, int sum, int sigma, const std::vector<int> &list) {
        if (int(list.size()) < 10 - k)
            return;
        ++stats.targets;
        int goal = m.sub(sigma, sum);
        if (k == 7) {
            // Once the first of the four vertices is fixed, find the other three
            // by their required sum, testing pair edges among them.
            for (std::size_t i = 0; i + 2 < list.size(); ++i) {
                int x = list[i], wanted = m.sub(goal, x);
                for (std::size_t j = i + 1; j + 1 < list.size(); ++j) {
                    int y = list[j], v = m.sub(wanted, y);
                    if (v <= y || !std::binary_search(list.begin() + j + 1, list.end(), v))
                        continue;
                    if (!edge(rows, sigma, x, y) || !edge(rows, sigma, x, v) ||
                        !edge(rows, sigma, y, v))
                        continue;
                    points[7] = x;
                    points[8] = y;
                    points[9] = v;
                    verify(7);
                }
            }
            return;
        }
        if (++epoch == 1000000000) {
            stamp.fill(0);
            epoch = 1;
        }
        pairs.clear();
        // Insert pairs strictly to the left of the current third vertex.
        for (std::size_t i = 2; i + 1 < list.size(); ++i) {
            int b = list[i - 1], c = list[i];
            for (std::size_t j = 0; j + 1 < i; ++j) {
                int a = list[j], s = m.add(a, b);
                if (!edge(rows, sigma, a, b))
                    continue;
                int prior = stamp[s] == epoch ? head[s] : -1;
                stamp[s] = epoch;
                head[s] = int(pairs.size());
                pairs.push_back({a, b, prior});
            }
            for (std::size_t j = i + 1; j < list.size(); ++j) {
                int d = list[j], s = m.sub(goal, m.add(c, d));
                if (stamp[s] != epoch || !edge(rows, sigma, c, d))
                    continue;
                for (int u = head[s]; u >= 0; u = pairs[u].next) {
                    const auto e = pairs[u];
                    if (!edge(rows, sigma, e.first, c) || !edge(rows, sigma, e.first, d) ||
                        !edge(rows, sigma, e.second, c) || !edge(rows, sigma, e.second, d))
                        continue;
                    points[6] = e.first;
                    points[7] = e.second;
                    points[8] = c;
                    points[9] = d;
                    verify(6);
                }
            }
        }
    }
    // Intersect the allowed points with sigma minus the holes of the ninth row.
    Bits hereditary(const Rows &rows, int k, int sum, const Bits &possible) const {
        Bits eligible{};
        eachBit(possible, m.words, [&](int x) {
            if (m.permits(rows, k, sum, x))
                m.set(eligible, x);
        });
        return eligible;
    }
    void graphs(const Rows &rows, int k, int sum, const Bits &domain, const Bits &H) {
        Bits possible = domain;
        if (normal.fast) {
            // The proposed k+1 point subset already has an all-ones sum.
            // Its representation using only the old points would rule out x.
            Bits noOld{}, zero{};
            m.shiftedUnion(noOld, holes(rows[k + 1]), zero, sum ? m.n - sum : 0);
            for (int j = 0; j < m.words; ++j)
                possible[j] &= noOld[j];
        }
        auto keep = [&](int s, int x) {
            return vertex(rows, s, x) && (!normal.fast || m.permits(rows, k, sum, x));
        };
        Bits gaps = holes(rows[9]);
        int gapCount = bits(gaps), candidateCount = bits(possible);
        if (candidateCount < 10 - k)
            return;
        eachBit(H, m.words, [&](int sigma) {
            auto &list = vertices[k];
            list.clear();
            if (gapCount < candidateCount) {
                eachBit(gaps, m.words, [&](int hole) {
                    int x = m.sub(sigma, hole);
                    if (m.has(possible, x) && keep(sigma, x))
                        list.push_back(x);
                });
                if (int(list.size()) < 10 - k)
                    return;
                std::sort(list.begin(), list.end());
            } else {
                eachBit(possible, m.words, [&](int x) {
                    if (keep(sigma, x))
                        list.push_back(x);
                });
            }
            targetGraph(rows, k, sum, sigma, list);
        });
    }
    void finishSix(const Rows &rows, int sum, const Bits &possible, const Bits &H, int count) {
        if (count <= sparseLimit) {
            ++stats.sparse;
            graphs(rows, 6, sum, possible, H);
            return;
        }
        ++stats.dense;
        Bits eligible = normal.fast ? hereditary(rows, 6, sum, possible) : possible;
        eachBit(eligible, m.words, [&](int x) {
            if (!normal.fast && !m.permits(rows, 6, sum, x))
                return;
            Rows child;
            m.adjoin(child, rows, x);
            if (!m.missingTarget(child))
                return;
            Bits next = nextMask(eligible, 6, x);
            trim(next, x, false);
            points[6] = x;
            graphs(child, 7, m.add(sum, x), next, holes(child[10]));
        });
    }
    void dfs(const Rows &rows, int k, int sum, const Bits &domain) {
        Bits possible = normal.fast ? hereditary(rows, k, sum, domain) : domain;
        eachBit(possible, m.words, [&](int x) {
            if (normal.cover && (x <= points[k - 1] || normal.color[x] != normal.color[points[3]]))
                return;
            int needed = normal.cover ? 6 - k : 10 - k;
            if (x > m.n - needed || (!normal.fast && !m.permits(rows, k, sum, x)))
                return;
            Rows child;
            m.adjoin(child, rows, x);
            if (k == 5) {
                ++stats.six;
                if (!m.missingTarget(child)) {
                    ++stats.covered;
                    return;
                }
                Bits H = holes(child[10]), next = nextMask(possible, k, x);
                trim(next, x, true);
                points[5] = x;
                finishSix(child, m.add(sum, x), next, H, bits(H));
            } else {
                Bits next = nextMask(possible, k, x);
                if (bits(next) < 9 - k)
                    return;
                points[k] = x;
                dfs(child, k + 1, m.add(sum, x), next);
            }
        });
    }
    // Complete a six-point list in its supplied order. Only the four as-yet
    // unchosen residues are ordered. The two pivots are zero and one.
    void fixedSix(const Points &prefix) {
        Rows rows{};
        for (auto &r : rows)
            r[0] = 1;
        Bits possible{};
        for (int x = 1; x < m.n; ++x)
            if (m.admissible[x])
                m.set(possible, x);
        int sum = 0;
        points[0] = 0;
        for (int k = 1; k < 6; ++k) {
            int x = prefix[k];
            if (!m.has(possible, x) || !m.permits(rows, k, sum, x))
                return;
            Rows child{};
            m.adjoin(child, rows, x);
            possible = nextMask(possible, k, x);
            points[k] = x;
            sum = m.add(sum, x);
            rows = child;
        }
        ++stats.six;
        Bits H = holes(rows[10]);
        if (bits(H))
            finishSix(rows, sum, possible, H, bits(H));
        else
            ++stats.covered;
    }
    // A one-sided outer rule gives {0,1,x,4-x}. Choose two of the six
    // unknown points in the same one of five colours to reach depth six.
    void outerPair(int x) {
        int mate = m.sub(4, x);
        if (x >= mate)
            return;
        int base[] = {0, 1, x, mate};
        Rows rows{};
        for (auto &r : rows)
            r[0] = 1;
        Bits cand{};
        for (int y = 1; y < m.n; ++y)
            if (m.admissible[y])
                m.set(cand, y);
        int sum = 0;
        points[0] = 0;
        for (int k = 1; k < 4; ++k) {
            int y = base[k];
            if (!m.has(cand, y) || !m.permits(rows, k, sum, y))
                return;
            Rows t{};
            m.adjoin(t, rows, y);
            cand = nextMask(cand, k, y);
            points[k] = y;
            rows = t;
            sum = m.add(sum, y);
        }
        cand = hereditary(rows, 4, sum, cand);
        eachBit(cand, m.words, [&](int y) {
            Rows five{};
            m.adjoin(five, rows, y);
            auto next = nextMask(cand, 4, y);
            points[4] = y;
            int total = m.add(sum, y);
            eachBit(next, m.words, [&](int v) {
                if (y >= v || y % 5 != v % 5 || !m.permits(five, 5, total, v))
                    return;
                Rows six{};
                m.adjoin(six, five, v);
                ++stats.six;
                auto H = holes(six[10]);
                int h = bits(H);
                if (!h) {
                    ++stats.covered;
                    return;
                }
                auto tail = nextMask(next, 5, v);
                points[5] = v;
                finishSix(six, m.add(total, v), tail, H, h);
            });
        });
    }
    void run(int fourth, const std::vector<int> &extra) {
        int prefix[6] = {0, 1, normal.z, fourth, 0, 0};
        if (extra.size() > 2)
            throw std::invalid_argument("at most two more prefix coordinates");
        std::copy(extra.begin(), extra.end(), prefix + 4);
        Rows rows{};
        for (auto &r : rows)
            r[0] = 1;
        Bits possible{};
        for (int x = 1; x < m.n; ++x)
            if (m.admissible[x])
                m.set(possible, x);
        int sum = 0, k = 1;
        for (; k < 4 + int(extra.size()); ++k) {
            int x = prefix[k];
            if (x <= points[k - 1] || x >= m.n || !m.has(possible, x) || !m.permits(rows, k, sum, x))
                return;
            Rows child{};
            m.adjoin(child, rows, x);
            possible = nextMask(possible, k, x);
            points[k] = x;
            sum = m.add(sum, x);
            rows = child;
            if (k == 2)
                trim(possible, normal.z, false);
        }
        if (k == 6) {
            Bits H = holes(rows[10]);
            ++stats.six;
            if (bits(H))
                finishSix(rows, sum, possible, H, bits(H));
            else
                ++stats.covered;
        } else
            dfs(rows, k, sum, possible);
    }
};

// The profile certificate forces a two-step singleton chain, or (near the
// upper end of this interval) one one-sided exchange in each outer square.
int profileSearch(int n, int threads, bool fast) {
    if (n < 712 || n > 723 || threads < 1)
        return 2;
    Modulus m(n, true);
    m.check();
    Normalization norm(m, 2, true, fast);
    std::atomic<int> job{0};
    std::mutex lock;
    std::vector<std::thread> pool;
    Statistics total;
    std::uint64_t tried = 0;
    for (int t = 0; t < threads; ++t)
        pool.emplace_back([&] {
            CliqueSearch search(norm);
            Points p{};
            p[1] = 1;
            std::uint64_t local = 0;
            auto run = [&]() {
                ++local;
                search.fixedSix(p);
            };
            for (;;) {
                int x = job.fetch_add(1);
                if (x >= n)
                    break;
                if (n >= 722)
                    search.outerPair(x);
                for (int u = 0; u < n; ++u) {
                    p[2] = x;
                    p[3] = (x + 2) % n;
                    p[4] = u;
                    p[5] = (u + 4) % n;
                    run();
                    if (n < 716 || n >= 722)
                        continue;
                    // Both outer exchanges use pairs, with x in their intersection.
                    p[2] = x;
                    p[3] = m.sub(4, x);
                    p[4] = m.sub(n - 2, x);
                    p[5] = u;
                    run();
                    // A one-point side and a two-point side. Reflection swaps arms.
                    // Of the six unspecified points two share a residue modulo 5.
                    if (x < u && x % 5 == u % 5) {
                        p[2] = n - 3;
                        p[3] = 7;
                        p[4] = x;
                        p[5] = u;
                        run();
                    }
                }
            }
            std::lock_guard<std::mutex> g(lock);
            tried += local;
            total.add(search.stats);
            for (auto a : search.leaves) {
                std::cout << "FOUND " << n;
                for (int x : a)
                    std::cout << ' ' << x;
                std::cout << '\n';
            }
        });
    for (auto &t : pool)
        t.join();
    std::cout << "profile " << n << " tried " << tried << " six " << total.six << " graphs "
              << total.targets << " cliques " << total.cliques << " valid " << total.valid
              << std::endl;
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 4 && (std::string(argv[1]) == "profile" || std::string(argv[1]) == "profile-fast"))
        return profileSearch(std::stoi(argv[2]), std::stoi(argv[3]),
                             std::string(argv[1]) == "profile-fast");
    if (argc < 6 || argc > 7) {
        std::cerr << "usage: round3_clique N z first-fourth last-fourth threads "
                     "[cover|cover-fast|fifth,sixth]\n";
        return 2;
    }
    int n = std::stoi(argv[1]), z = std::stoi(argv[2]), lo = std::stoi(argv[3]),
        hi = std::stoi(argv[4]);
    int threads = std::stoi(argv[5]);
    if (n < 512 || n > 1024 || z < 2 || z > n - 8 || lo < z + 1 || hi < lo || threads < 1)
        return 2;
    Modulus m(n, true);
    m.check();
    bool fast = argc == 7 && std::string(argv[6]) == "cover-fast";
    bool cover = fast || (argc == 7 && std::string(argv[6]) == "cover");
    Normalization norm(m, z, cover, fast);
    std::vector<int> extra;
    if (argc == 7 && !cover) {
        if (lo != hi)
            return 2;
        std::stringstream in(argv[6]);
        std::string part;
        while (std::getline(in, part, ','))
            extra.push_back(std::stoi(part));
        if (extra.size() > 2)
            return 2;
    }
    int top = std::min(hi, cover ? n - 3 : n - 7);
    std::atomic<int> job{top};
    std::mutex lock;
    std::vector<std::thread> pool;
    Statistics total;
    int finished = 0;
    for (int t = 0; t < threads; ++t)
        pool.emplace_back([&] {
            while (true) {
                int fourth = job.fetch_sub(1);
                if (fourth < lo)
                    break;
                CliqueSearch search(norm);
                search.run(fourth, extra);
                std::lock_guard<std::mutex> guard(lock);
                for (auto A : search.leaves) {
                    std::cout << "FOUND " << n;
                    for (int x : A)
                        std::cout << ' ' << x;
                    std::cout << '\n';
                }
                total.add(search.stats);
                ++finished;
                std::cout << "fourth " << n << ' ' << z << ' ' << fourth << ' ' << search.stats.six
                          << ' ' << search.stats.targets << ' ' << search.stats.valid << '\n';
                if (finished % 8 == 0 || !search.leaves.empty())
                    std::cout.flush();
            }
        });
    for (auto &t : pool)
        t.join();
    std::cout << "complete " << n << ' ' << z << ' ' << lo << ' ' << top << " fourths " << finished
              << " six " << total.six << " covered " << total.covered << " sparse " << total.sparse
              << " dense " << total.dense << " target-graphs " << total.targets << " cliques "
              << total.cliques << " valid " << total.valid << " method "
              << (fast    ? "cover-fast"
                  : cover ? "cover"
                          : "sorted")
              << std::endl;
}
