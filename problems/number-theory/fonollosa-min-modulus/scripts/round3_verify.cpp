// Independent verifier for the normalized ten-set endpoint. Coordinates are
// appended in increasing order. At six or seven points it imposes the final
// sum and enumerates the last coordinates by three or two nested loops.
#include <algorithm>
#include <array>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <numeric>
#include <string>
#include <thread>
#include <vector>
using U = std::uint64_t;
using Mask = std::array<U, 17>; // sentinel for unaligned reads
using Table = std::array<Mask, 11>;
struct Model {
    int n, z, words;
    bool cover;
    int color(int x) const { return ((211 * x + 17) % n) % 3; }
    U tail;
    std::vector<Mask> ok, later, laterColor;
    int index(int a, int b) const {
        if (a > b)
            std::swap(a, b);
        return a * (2 * n - a - 1) / 2 + b - a - 1;
    }
    Model(int n_, int z_, bool cover_, bool upper = false)
        : n(n_), z(z_), words((n + 63) / 64), cover(cover_),
          tail(n % 64 ? (U(1) << (n % 64)) - 1 : ~U(0)), ok(upper ? 0 : n * (n - 1) / 2), later(n),
          laterColor(n) {
        if (upper)
            return;
        if (cover)
            for (int x = 0; x < n; ++x)
                for (int y = 0; y < n; ++y) {
                    if (y > x)
                        later[x][y / 64] |= U(1) << (y % 64);
                    if (y > x || color(x) != color(y))
                        laterColor[x][y / 64] |= U(1) << (y % 64);
                }
        // Mark forbidden triples by generating the whole affine orbit of each
        // smaller normalized third coordinate, including all choices of origin.
        std::vector<unsigned char> forbidden(n * n);
        for (int t = 2; t < z; ++t)
            for (int u = 1; u < n; ++u)
                if (std::gcd(u, n) == 1) {
                    int v[] = {0, u, t * u % n};
                    for (int i = 0; i < 3; ++i) {
                        int j = (n + v[(i + 1) % 3] - v[i]) % n, k = (n + v[(i + 2) % 3] - v[i]) % n;
                        forbidden[n * std::min(j, k) + std::max(j, k)] = 1;
                    }
                }
        for (int a = 0; a < n; ++a)
            for (int b = a + 1; b < n; ++b) {
                auto &row = ok[index(a, b)];
                for (int c = b + 1; c < n; ++c)
                    if (!forbidden[n * (b - a) + c - a]) {
                        row[c / 64] |= U(1) << (c % 64);
                        if (cover) {
                            ok[index(a, c)][b / 64] |= U(1) << (b % 64);
                            ok[index(b, c)][a / 64] |= U(1) << (a % 64);
                        }
                    }
            }
    }
    bool member(const Mask &b, int x) const { return (b[x / 64] >> (x % 64)) & 1; }
    int minus(int a, int b) const { return a >= b ? a - b : a - b + n; }
    template <class F> void each(const Mask &m, F f) const {
        for (int w = 0; w < words; ++w)
            for (auto bits = m[w]; bits; bits &= bits - 1)
                f(w * 64 + __builtin_ctzll(bits));
    }
    Mask complement(const Mask &b) const {
        Mask a{};
        for (int w = 0; w < words; ++w)
            a[w] = ~b[w];
        a[words - 1] &= tail;
        return a;
    }
    int size(const Mask &b) const {
        int s = 0;
        for (int w = 0; w < words; ++w)
            s += __builtin_popcountll(b[w]);
        return s;
    }
    U circular(const Mask &m, int s) const {
        int j = s / 64, off = s % 64;
        U v = m[j] >> off;
        if (off)
            v |= m[j + 1] << (64 - off);
        int left = n - s;
        if (left < 64)
            v |= m[0] << left;
        return v;
    }
    void extend(const Table &t, int x, Table &out) const {
        out[0] = t[0];
        for (int k = 1; k <= 10; ++k) {
            int s = n - x;
            for (int w = 0; w < words; ++w) {
                out[k][w] = t[k][w] | circular(out[k - 1], s);
                s += 64;
                if (s >= n)
                    s -= n;
            }
            out[k][words - 1] &= tail;
            out[k][words] = 0;
        }
    }
    bool validExtension(const Table &t, int k, int total, int x) const {
        // For the new all-ones sum, exclude exactly the counts of x other than one.
        int s = (total + x) % n;
        for (int h = 0; h <= k + 1; ++h) {
            if (h != 1 && member(t[k + 1 - h], s))
                return false;
            s = minus(s, x);
        }
        return true;
    }
    bool allowedSum(const Table &t, int s, int x) const {
        for (int h = 1; h <= 10; ++h) {
            s = minus(s, x);
            if (member(t[10 - h], s))
                return false;
        }
        return true;
    }
};
struct Search {
    explicit Search(const Model &model) : m(model) {}
    const Model &m;
    std::array<int, 10> a{};
    U six = 0, checked = 0, valid = 0;
    std::vector<std::array<int, 10>> found;
    Mask next(const Mask &mask, int k, int x) const {
        Mask v = mask;
        for (int i = 0; i < k; ++i) {
            auto &row = m.ok[m.index(a[i], x)];
            for (int w = 0; w < m.words; ++w)
                v[w] &= row[w];
        }
        return v;
    }
    void trim(Mask &mask, int x, bool colorOnly) const {
        if (!m.cover)
            return;
        const auto &allowed = colorOnly ? m.laterColor[x] : m.later[x];
        for (int i = 0; i < m.words; ++i)
            mask[i] &= allowed[i];
    }
    void test(const Table &t, int k, int sum) {
        // Directly test every completion with the specified sum. This verifier
        // needs no adjacency graph and uses no target-sum pair-edge pruning.
        ++checked;
        Table children[4]{};
        auto prev = &t;
        for (int i = k; i < 10; ++i) {
            if (!m.validExtension(*prev, i, sum, a[i]))
                return;
            if (i < 9) {
                m.extend(*prev, a[i], children[i - k]);
                prev = &children[i - k];
            }
            sum = (sum + a[i]) % m.n;
        }
        ++valid;
        found.push_back(a);
    }
    void tails(const Table &t, int k, int sum, const Mask &domain, const Mask &holes) {
        Mask cand = domain;
        const auto gaps = m.complement(t[9]);
        int nG = m.size(gaps);
        bool shift = m.cover && m.size(holes) >= 4 && nG > 12;
        Mask reflected{};
        if (shift) {
            m.each(gaps, [&](int g) {
                int u = g ? m.n - g : 0;
                reflected[u / 64] |= U(1) << (u % 64);
            });
            for (int w = 0; w < m.words; ++w)
                cand[w] &= ~m.circular(t[k + 1], (64 * w + sum) % m.n);
            m.each(cand, [&](int x) {
                if (!m.validExtension(t, k, sum, x))
                    cand[x / 64] &= ~(U(1) << (x % 64));
            });
        }
        int nC = m.size(cand);
        if (nC < 10 - k)
            return;
        m.each(holes, [&](int s) {
            std::array<int, 1024> v;
            int count = 0;
            Mask eligible{};
            auto tryPoint = [&](int x) {
                if (m.allowedSum(t, s, x) && (!m.cover || shift || m.validExtension(t, k, sum, x))) {
                    v[count++] = x;
                    eligible[x / 64] |= U(1) << (x % 64);
                }
            };
            if (shift) {
                Mask usable{};
                int offset = s ? m.n - s : 0;
                for (int w = 0; w < m.words; ++w) {
                    usable[w] = cand[w] & m.circular(reflected, offset);
                    offset += 64;
                    if (offset >= m.n)
                        offset -= m.n;
                }
                m.each(usable, tryPoint);
            } else if (nG < nC) {
                m.each(gaps, [&](int g) {
                    int x = m.minus(s, g);
                    if (m.member(cand, x))
                        tryPoint(x);
                });
                if (count < 10 - k)
                    return;
                std::sort(v.begin(), v.begin() + count);
            } else
                m.each(cand, tryPoint);
            int goal = m.minus(s, sum);
            for (int i = 0; i < count - (9 - k); ++i) {
                int x = v[i];
                a[k] = x;
                int need = m.minus(goal, x);
                for (int j = i + 1; j < count - (8 - k); ++j) {
                    int y = v[j];
                    a[k + 1] = y;
                    int d = m.minus(need, y);
                    if (k == 7) {
                        if (d > y && m.member(eligible, d)) {
                            a[9] = d;
                            test(t, k, sum);
                        }
                    } else
                        for (int l = j + 1; l < count - 1; ++l) {
                            int h = v[l], last = m.minus(d, h);
                            if (last > h && m.member(eligible, last)) {
                                a[8] = h;
                                a[9] = last;
                                test(t, k, sum);
                            }
                        }
                }
            }
        });
    }
    void dfs(const Table &t, int k, int sum, const Mask &cand) {
        if (k >= 6) {
            if (k == 6)
                ++six;
            auto holes = m.complement(t[10]);
            int h = m.size(holes);
            if (h == 0)
                return;
            if (k == 7 || h <= 30) {
                tails(t, k, sum, cand, holes);
                return;
            }
        }
        m.each(cand, [&](int x) {
            if (m.cover && k <= 5 && (x <= a[k - 1] || m.color(x) != m.color(a[3])))
                return;
            int maximum = m.cover && k <= 5 ? m.n - 6 + k : m.n - 10 + k;
            if (x > maximum || !m.validExtension(t, k, sum, x))
                return;
            auto after = next(cand, k, x);
            if (k == 5)
                trim(after, x, true);
            if (k == 6)
                trim(after, x, false);
            if (m.size(after) < 9 - k)
                return;
            Table child{};
            m.extend(t, x, child);
            a[k] = x;
            dfs(child, k + 1, (sum + x) % m.n, after);
        });
    }
    void shard(int fourth, const std::vector<int> &extra) {
        if (fourth > (m.cover ? m.n - 3 : m.n - 7))
            return;
        std::vector<int> p = {0, 1, m.z, fourth};
        p.insert(p.end(), extra.begin(), extra.end());
        Mask cand{};
        for (int y = 1; y < m.n; ++y)
            cand[y / 64] |= U(1) << (y % 64);
        Table t{};
        for (auto &r : t)
            r[0] = 1;
        int sum = 0;
        for (int i = 1; i < int(p.size()); ++i) {
            int x = p[i];
            if (x <= a[i - 1] || x >= m.n || !m.member(cand, x) || !m.validExtension(t, i, sum, x))
                return;
            auto after = next(cand, i, x);
            Table child{};
            m.extend(t, x, child);
            t = child;
            cand = after;
            if (i == 2)
                trim(cand, m.z, false);
            a[i] = x;
            sum = (sum + x) % m.n;
        }
        dfs(t, p.size(), sum, cand);
    }
};
// For the large-third-coordinate interval, most normalizations have few
// admissible triples. Generate their minima once by affine images. Filter
// each sorted candidate list directly, avoiding a cubic mask table per shard.
struct Upper {
    Model m;
    std::vector<int> minimum;
    explicit Upper(int n) : m(n, 2, false, true), minimum(n * n, n) {
        for (int u = 1; u < n; ++u)
            if (std::gcd(u, n) == 1)
                for (int t = 2; t < n; ++t) {
                    int a[3] = {0, u, u * t % n};
                    for (int i = 0; i < 3; ++i) {
                        int j = m.minus(a[(i + 1) % 3], a[i]), k = m.minus(a[(i + 2) % 3], a[i]);
                        auto &cell = minimum[n * std::min(j, k) + std::max(j, k)];
                        cell = std::min(cell, t);
                    }
                }
    }
    bool triple(int x, int y, int v, int z) const { return minimum[(y - x) * m.n + v - x] >= z; }
    void descend(Search &s, const Table &t, int k, int sum, int z, const Mask &cand) const {
        auto eligible = cand;
        m.each(cand, [&](int x) {
            if (!m.validExtension(t, k, sum, x))
                eligible[x / 64] &= ~(U(1) << (x % 64));
        });
        if (m.size(eligible) < 10 - k)
            return;
        if (k >= 6) {
            if (k == 6)
                ++s.six;
            const auto holes = m.complement(t[10]);
            const int count = m.size(holes);
            if (!count)
                return;
            if (k == 7 || count <= 30) {
                s.tails(t, k, sum, eligible, holes);
                return;
            }
        }
        m.each(eligible, [&](int x) {
            if (x > m.n - (10 - k))
                return;
            Mask later{};
            m.each(eligible, [&](int y) {
                if (y <= x)
                    return;
                for (int i = 0; i < k; ++i)
                    if (!triple(s.a[i], x, y, z))
                        return;
                later[y / 64] |= U(1) << (y % 64);
            });
            if (m.size(later) < 9 - k)
                return;
            s.a[k] = x;
            Table next{};
            m.extend(t, x, next);
            descend(s, next, k + 1, (sum + x) % m.n, z, later);
        });
    }
    void start(Search &s, int z) const {
        if (!triple(0, 1, z, z))
            return;
        s.a[0] = 0;
        s.a[1] = 1;
        s.a[2] = z;
        Table a{}, b{}, t{};
        for (auto &row : a)
            row[0] = 1;
        m.extend(a, 1, b);
        if (!m.validExtension(b, 2, 1, z))
            return;
        m.extend(b, z, t);
        Mask cand{};
        for (int y = z + 1; y < m.n; ++y)
            if (triple(0, 1, y, z) && triple(0, z, y, z) && triple(1, z, y, z))
                cand[y / 64] |= U(1) << (y % 64);
        descend(s, t, 3, (1 + z) % m.n, z, cand);
    }
};

// Check all suffixes after a prescribed (possibly unsorted) six-point prefix.
void fixedPrefix(Search &s, const std::array<int, 6> &p) {
    const auto &m = s.m;
    Table t{};
    for (auto &row : t)
        row[0] = 1;
    Mask cand{};
    for (int x = 1; x < m.n; ++x)
        cand[x / 64] |= U(1) << (x % 64);
    int sum = 0;
    s.a[0] = 0;
    for (int j = 1; j < 6; ++j) {
        int x = p[j];
        if (!m.member(cand, x) || !m.validExtension(t, j, sum, x))
            return;
        auto after = s.next(cand, j, x);
        Table child{};
        m.extend(t, x, child);
        s.a[j] = x;
        cand = after;
        t = child;
        sum = (sum + x) % m.n;
    }
    s.dfs(t, 6, sum, cand);
}

int profileRange(int n, int threads) {
    if (n < 712 || n > 723 || threads < 1)
        return 2;
    Model m(n, 2, true);
    std::atomic<int> job{n - 1};
    std::mutex lock;
    std::vector<std::thread> pool;
    U six = 0, checked = 0, valid = 0;
    for (int w = 0; w < threads; ++w)
        pool.emplace_back([&] {
            Search s{m};
            for (;;) {
                int x = job.fetch_sub(1);
                if (x < 0)
                    break;
                if (n >= 722 && x < m.minus(4, x)) {
                    // Fix a different colour assignment from the primary test.
                    for (int y = 0; y < n; ++y)
                        for (int v = y + 1; v < n; ++v)
                            if ((17 * y % n) % 5 == (17 * v % n) % 5)
                                fixedPrefix(s, {0, 1, m.minus(4, x), x, y, v});
                }
                for (int y = 0; y < n; ++y) {
                    fixedPrefix(s, {0, 1, (x + 2) % n, x, (y + 4) % n, y});
                    if (n < 720 || n >= 722)
                        continue;
                    fixedPrefix(s, {0, 1, m.minus(n - 2, x), m.minus(4, x), x, y});
                    // Six free coordinates give at least two with the same colour.
                    if (y > x && (x * 17 % n) % 5 == (y * 17 % n) % 5)
                        fixedPrefix(s, {0, 1, 7, n - 3, x, y});
                }
            }
            std::lock_guard<std::mutex> g(lock);
            six += s.six;
            checked += s.checked;
            valid += s.valid;
            for (auto &a : s.found) {
                std::cout << "found " << n;
                for (int x : a)
                    std::cout << ' ' << x;
                std::cout << '\n';
            }
        });
    for (auto &w : pool)
        w.join();
    std::cout << "profile-verified " << n << " six " << six << " ten " << checked << " valid "
              << valid << std::endl;
    return 0;
}

// A generating ten-set in an even group of order below 1024 has an
// opposite-parity pair. If its difference is a nonunit, a unit scaling
// normalizes that pair to 0,g with odd g>1. For an odd prime p|g, the
// subgroup pZ has order below 352, so it cannot contain a valid nine-set.
int nonunitRange(int n, int threads) {
    if (n < 704 || n >= 1024 || n % 2 || threads < 1)
        return 2;
    Model m(n, 2, true);
    std::vector<Mask> nonunit(n);
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b)
            if (a != b && std::gcd(n, std::abs(a - b)) > 1)
                nonunit[a][b / 64] |= U(1) << (b % 64);
    for (int a = 0; a < n; ++a)
        for (int b = a + 1; b < n; ++b) {
            auto &row = m.ok[m.index(a, b)];
            row = {};
            if (m.member(nonunit[a], b))
                for (int i = 0; i < m.words; ++i)
                    row[i] = nonunit[a][i] & nonunit[b][i];
        }
    struct Job {
        int g, p, z;
    };
    std::vector<Job> jobs;
    for (int g = 3; g < n; g += 2)
        if (n % g == 0) {
            // Choose the least gcd among opposite-parity pairs. Their differences
            // generate all differences: subtract the two differences to a common
            // opposite-parity point. So the admissible odd gcds must be coprime
            // as a family. At 1014 this leaves only g=3.
            int common = n;
            for (int h = g; h < n; h += 2)
                if (n % h == 0)
                    common = std::gcd(common, h);
            if (common != 1)
                continue;
            int p = 3;
            while (g % p)
                p += 2;
            for (int z = 1; z < n; ++z)
                if (z % p && m.member(m.ok[m.index(0, g)], z))
                    jobs.push_back({g, p, z});
        }
    std::atomic<std::size_t> job{0};
    std::mutex lock;
    std::vector<std::thread> pool;
    U six = 0, checked = 0, valid = 0;
    for (int worker = 0; worker < threads; ++worker)
        pool.emplace_back([&] {
            Search s{m};
            for (;;) {
                auto id = job.fetch_add(1);
                if (id >= jobs.size())
                    break;
                const int g = jobs[id].g;
                const int p = jobs[id].p;
                const int z = jobs[id].z;
                Table one{}, two{}, three{};
                for (auto &r : one)
                    r[0] = 1;
                m.extend(one, g, two);
                if (!m.validExtension(two, 2, g, z))
                    continue;
                m.extend(two, z, three);
                s.a[0] = 0;
                s.a[1] = g;
                s.a[2] = z;
                auto cand = s.next(m.ok[m.index(0, g)], 2, z);
                int sum3 = (g + z) % n;
                m.each(cand, [&](int w) {
                    if (w <= z || w % p == 0 || !m.validExtension(three, 3, sum3, w))
                        return;
                    auto rest = s.next(cand, 3, w);
                    Table four{};
                    m.extend(three, w, four);
                    int sum4 = (sum3 + w) % n;
                    s.a[3] = w;
                    m.each(rest, [&](int x) {
                        if ((x % p && x < w) || !m.validExtension(four, 4, sum4, x))
                            rest[x / 64] &= ~(U(1) << (x % 64));
                    });
                    if (m.size(rest) < 6)
                        return;
                    m.each(rest, [&](int x) {
                        auto next = s.next(rest, 4, x);
                        Table five{};
                        m.extend(four, x, five);
                        int sum5 = (sum4 + x) % n;
                        s.a[4] = x;
                        m.each(next, [&](int y) {
                            if (y <= x || y % 5 != x % 5 || !m.validExtension(five, 5, sum5, y))
                                return;
                            auto tail = s.next(next, 5, y);
                            Table t{};
                            m.extend(five, y, t);
                            s.a[5] = y;
                            s.dfs(t, 6, (sum5 + y) % n, tail);
                        });
                    });
                });
            }
            std::lock_guard<std::mutex> g(lock);
            six += s.six;
            checked += s.checked;
            valid += s.valid;
            for (auto &a : s.found) {
                std::cout << "found " << n;
                for (int x : a)
                    std::cout << ' ' << x;
                std::cout << '\n';
            }
        });
    for (auto &w : pool)
        w.join();
    std::cout << "nonunit " << n << " roots " << jobs.size() << " six " << six << " ten " << checked
              << " valid " << valid << std::endl;
    return 0;
}

int upperRange(int n, int lo, int hi, int threads) {
    if (n < 512 || n > 1024 || lo < 2 || hi < lo || hi > n - 8 || threads < 1)
        return 2;
    Upper u(n);
    std::atomic<int> job{hi};
    std::mutex lock;
    std::vector<std::thread> pool;
    for (int w = 0; w < threads; ++w)
        pool.emplace_back([&] {
            for (;;) {
                int z = job.fetch_sub(1);
                if (z < lo)
                    break;
                Search s{u.m};
                u.start(s, z);
                std::lock_guard<std::mutex> guard(lock);
                for (auto &a : s.found) {
                    std::cout << "found " << n;
                    for (int x : a)
                        std::cout << ' ' << x;
                    std::cout << '\n';
                }
                std::cout << "upper " << n << ' ' << z << " six " << s.six << " ten " << s.checked
                          << " valid " << s.valid << std::endl;
            }
        });
    for (auto &w : pool)
        w.join();
    return 0;
}
int main(int argc, char **argv) {
    if (argc == 4 && std::string(argv[1]) == "nonunit")
        return nonunitRange(std::atoi(argv[2]), std::atoi(argv[3]));
    if (argc == 4 && std::string(argv[1]) == "profile")
        return profileRange(std::atoi(argv[2]), std::atoi(argv[3]));
    if (argc == 6 && std::string(argv[1]) == "upper")
        return upperRange(std::atoi(argv[2]), std::atoi(argv[3]), std::atoi(argv[4]),
                          std::atoi(argv[5]));
    if (argc != 6 && argc != 7 && argc != 8)
        return 2;
    bool cover = argc == 7 && std::string(argv[6]) == "cover";
    if (argc == 7 && !cover)
        return 2;
    int n = std::atoi(argv[1]), z = std::atoi(argv[2]), lo = std::atoi(argv[3]),
        hi = std::atoi(argv[4]), threads = std::atoi(argv[5]);
    if (n < 512 || n > 1024 || z < 2 || z > n - 8 || lo <= z || hi < lo || threads < 1)
        return 2;
    std::vector<int> extra;
    if (argc == 8) {
        if (lo != hi)
            return 2;
        extra = {std::atoi(argv[6]), std::atoi(argv[7])};
    }
    Model m(n, z, cover);
    std::atomic<int> work{lo};
    std::mutex lock;
    std::vector<std::thread> pool;
    int done = 0;
    U six = 0, checked = 0, valid = 0;
    for (int w = 0; w < threads; ++w)
        pool.emplace_back([&] {
            for (;;) {
                int x = work.fetch_add(1);
                if (x > std::min(cover ? n - 3 : n - 7, hi))
                    break;
                Search s{m};
                s.shard(x, extra);
                std::lock_guard<std::mutex> guard(lock);
                for (auto &a : s.found) {
                    std::cout << "found " << n;
                    for (int y : a)
                        std::cout << ' ' << y;
                    std::cout << '\n';
                }
                ++done;
                six += s.six;
                checked += s.checked;
                valid += s.valid;
            }
        });
    for (auto &w : pool)
        w.join();
    std::cout << "verified " << n << ' ' << z << " fourths " << done << " six " << six << " ten "
              << checked << " valid " << valid << " method " << (cover ? "cover" : "sorted")
              << std::endl;
}
