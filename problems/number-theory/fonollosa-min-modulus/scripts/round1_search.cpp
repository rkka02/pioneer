// Exact tests for sets consisting of binary coins and two additional integers.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

using Int = std::int64_t;
using Pair = std::array<Int, 2>;

Int power(int e) { return Int{1} << e; }

Int endpoint(int n) {
    int p = 1;
    while (p * 2 <= n) p *= 2;
    return power(n) - p;
}

Int residue(Int x, Int modulus) {
    Int r = x % modulus;
    return r < 0 ? r + modulus : r;
}

// Powers 1,...,high. A split raises the coin count by one, up to the value.
bool attainable(Int value, int coins, Int high) {
    return value >= coins && value <= coins * high &&
        value / high + __builtin_popcountll(value % high) <= coins;
}

struct BinaryCore {
    int n;
    Int high;
    Int coreSum;

    explicit BinaryCore(int size)
        : n(size), high(power(n - 3)), coreSum(2 * high - 1) {}

    // Each bad pair of outlier multiplicities contributes one. At (1,1)
    // the baseline integer sum has a unique minimal-coin representation.
    // modulus == 0 selects exact equality in the integers.
    int score(Pair out, Int modulus, int stop = std::numeric_limits<int>::max()) const {
        int bad = 0;
        for (int i = 0; i <= n; ++i) {
            for (int j = 0; i + j <= n; ++j) {
                int coins = n - i - j;
                Int value = coreSum + (1 - i) * out[0] + (1 - j) * out[1];
                auto collision = [&](Int s) {
                    return !(i == 1 && j == 1 && s == coreSum) &&
                        attainable(s, coins, high);
                };
                bool hits = false;
                if (modulus == 0) {
                    hits = collision(value);
                } else {
                    for (Int s = residue(value, modulus); s <= coins * high; s += modulus) {
                        if (collision(s)) { hits = true; break; }
                    }
                }
                if (hits && ++bad >= stop) return bad;
            }
        }
        return bad;
    }

    Int minimum(Pair out) const {
        if (score(out, 0, 1)) return 0; // No modulus preserves a valid n-tuple.
        Int sum = coreSum + out[0] + out[1];
        Int low = std::min({Int{1}, out[0], out[1]});
        Int top = std::max({high, out[0], out[1]});
        Int limit = std::max(sum - n * low, n * top - sum) + 1;
        for (Int mod = power(n - 1); mod <= limit; ++mod) {
            if (score(out, mod, 1) == 0) return mod;
        }
        throw std::logic_error("integer-valid set passed its diameter bound");
    }
};

// A second implementation for small controls. Counts unordered representations
// of the target modulo N, saturating at two. Equal residues of different
// input entries remain labelled, so a loss of cardinality is also rejected.
bool direct(const std::vector<Int>& a, int mod) {
    int n = static_cast<int>(a.size());
    std::vector<std::vector<unsigned char>> dp(n + 1, std::vector<unsigned char>(mod));
    dp[0][0] = 1;
    Int target = 0;
    for (Int x : a) {
        target += x;
        int shift = static_cast<int>(residue(x, mod));
        for (int k = 1; k <= n; ++k) {
            for (int s = 0; s < mod; ++s) {
                int t = s + shift;
                if (t >= mod) t -= mod;
                dp[k][t] = std::min(2, dp[k][t] + dp[k - 1][s]);
            }
        }
    }
    return dp[n][residue(target, mod)] == 1;
}

void controls() {
    std::mt19937_64 rng(308366);
    int checks = 0;
    for (int n = 4; n <= 10; ++n) {
        BinaryCore core(n);
        for (int t = 0; t < 180; ++t) {
            int mod = 1 + rng() % (2 * power(n));
            Pair out{static_cast<Int>(rng() % (2 * mod)) - mod,
                     static_cast<Int>(rng() % (2 * mod)) - mod};
            if (t < 3) {
                mod = static_cast<int>(endpoint(n)) + t - 1;
                out = {2 * core.high, 4 * core.high};
            }
            std::vector<Int> a;
            for (int i = 0; i < n - 2; ++i) a.push_back(power(i));
            a.insert(a.end(), out.begin(), out.end());
            if ((core.score(out, mod, 1) == 0) != direct(a, mod))
                throw std::logic_error("oracle disagreement");
            ++checks;
        }
    }
    std::cout << "direct DP cross-checks " << checks << '\n';
}

// Independently test the equal consecutive gaps in the difference vectors
// of Bohman Sections 2 and 4. A prefix ending after those two gaps has a
// three-term arithmetic progression among its suffix sums, whatever follows.
void progression_controls() {
    std::vector<std::vector<int>> seeds{{1,1}, {2,1,1,4}, {4,1,1,2,8},
        {8,2,1,1,4,16}, {16,4,1,1,2,8,32}};
    int cases = 0;
    for (const auto& seed : seeds) {
        for (int n = 8; n <= 25; ++n) {
            // Subtract the shared suffix; any tail gives the same certificate.
            std::vector<int> values;
            int total = 0;
            for (int gap : seed) { values.push_back(-total); total += gap; }
            values.push_back(-total);
            bool found = false;
            for (unsigned j = 1; j + 1 < values.size(); ++j)
                found |= values[j - 1] + values[j + 1] == 2 * values[j];
            if (n <= static_cast<int>(seed.size()) || !found)
                throw std::logic_error("missing progression");
            ++cases;
        }
    }
    std::cout << "Conway-Guy/Lunnon prefix certificates " << cases << '\n';
}

// Build the actual Conway-Guy suffix sums. The nearest integer to sqrt(2*i)
// changes at half-integers, whose squares cannot be integers.
void classical_integer_tests() {
    std::vector<Int> gaps{1};
    int tested = 0;
    for (int n = 2; n <= 25; ++n) {
        int guide = 0;
        while ((2*guide+1)*(2*guide+1) < 8*(n-1)) ++guide;
        Int next = 0;
        for (int j = n-1-guide; j < n-1; ++j) next += gaps[j];
        gaps.push_back(next);
        if (n < 8) continue;
        std::vector<Int> suffix(n);
        Int total = 0;
        for (int j = n-1; j >= 0; --j) suffix[j] = (total += gaps[j]);
        if (suffix[0] + suffix[2] != 2*suffix[1])
            throw std::logic_error("Conway-Guy relation failed");
        if (n == 8 && suffix != std::vector<Int>{84,83,82,80,77,71,60,40})
            throw std::logic_error("Conway-Guy sequence mismatch");
        Int a = 1, b = 2;
        for (int i = 3; i < n; ++i) {
            if (a + (a + 2*b) != 2*(a+b))
                throw std::logic_error("Fibonacci relation failed");
            Int c = a+b; a = b; b = c;
        }
        ++tested;
    }
    std::cout << "actual Conway-Guy and Fibonacci sizes " << tested << '\n';
}

void greedy_test(int n) {
    // The previous n-1 greedy values, shifted by one, are powers up to H.
    Int H = power(n-2);
    for (Int y = H+1; y < 2*H; ++y)
        if (!attainable(2*H-1+y, n, H))
            throw std::logic_error("greedy extension skipped a candidate");
    BinaryCore core(n);
    Pair binary{2*core.high, 4*core.high};
    if (core.score(binary, 0, 1) || core.minimum(binary) != endpoint(n))
        throw std::logic_error("binary endpoint control failed");
}

void doubled_core(int n) {
    int r = n - 1;
    Int high = power(r - 1), sum = 2 * high - 1;
    Int checked = 0, validBases = 0, surviveThree = 0, valid = 0;
    for (Int M = endpoint(r); 2 * M < endpoint(n); ++M) {
        bool base = true;
        for (Int s = sum % M; s <= r * high; s += M)
            if (s != sum && attainable(s, r, high)) base = false;
        if (!base) continue;
        ++validBases;
        for (Int x = 1; x < 2 * M; x += 2) {
            ++checked;
            bool collision = false;
            for (int t = 1; 2 * t <= r && !collision; ++t) {
                int coins = r - 2 * t;
                for (Int s = residue(sum - t * x, M); s <= coins * high; s += M) {
                    if (attainable(s, coins, high)) { collision = true; break; }
                }
                if (t == 1 && !collision) ++surviveThree;
            }
            if (!collision) {
                ++valid;
                std::cout << "candidate doubled " << n << ' ' << 2*M << ' ' << x << '\n';
            }
        }
    }
    std::cout << "doubled " << n << ' ' << validBases << ' ' << checked << ' '
              << surviveThree << ' ' << valid << '\n';
}

// The only viable classes of the two extras mod 4 are an odd x and 2*y
// for odd y. Dividing the even subset by 2 first tests the y coordinate.
void quadrupled_core(int n) {
    BinaryCore core(n);
    int m = n-2;
    Int evenSets = 0, fullTests = 0, wins = 0;
    for (Int M = endpoint(m); 4*M < endpoint(n); ++M) {
        bool base = true;
        for (Int s = core.coreSum % M; s <= m*core.high; s += M)
            if (s != core.coreSum && attainable(s,m,core.high)) base = false;
        if (!base) continue;
        for (Int y = 1; y < 2*M; y += 2) {
            bool evenValid = true;
            for (int t = 1; 2*t <= m && evenValid; ++t) {
                int slots = m-2*t;
                for (Int s = residue(core.coreSum-t*y,M); s <= slots*core.high; s += M)
                    if (attainable(s,slots,core.high)) { evenValid = false; break; }
            }
            if (!evenValid) continue;
            ++evenSets;
            for (int w = 0; w < n-3; ++w) {
                Int first = residue(y+2*(core.coreSum-w),2*M);
                for (Int x = first; x < 4*M; x += 2*M) {
                    ++fullTests;
                    bool collision = false;
                    for (int i = 3; i <= n && !collision; i += 2) {
                        for (int j = 0; i+j <= n && !collision; ++j) {
                            Int shift = (1-i)*x+2*(1-j)*y;
                            if (shift%4) continue;
                            int slots = n-i-j;
                            for (Int s = residue(core.coreSum+shift/4,M);
                                 s <= slots*core.high; s += M)
                                if (attainable(s,slots,core.high)) { collision = true; break; }
                        }
                    }
                    if (!collision) {
                        ++wins;
                        std::cout << "candidate quadrupled " << n << ' ' << 4*M << ' '
                                  << x << ' ' << 2*y << std::endl;
                    }
                }
            }
        }
    }
    std::cout << "quadrupled " << n << ' ' << evenSets << ' ' << fullTests << ' '
              << wins << std::endl;
}

struct AnnealingResult {
    Pair out;
    int score;
};

// The walk uses exact integer scores. A worsening by d at temperature T is
// accepted with probability 2^(-ceil(d/T)). Keep distinct ordered proposals
// per modulus for reproducible reporting and to avoid counting repeat visits.
AnnealingResult anneal(const BinaryCore& core, Int mod, std::mt19937_64& rng,
                       int& proposals, int& validCount) {
    std::set<Pair> seen;
    int best = std::numeric_limits<int>::max();
    Pair saved{};
    for (int run = 0; run < 5; ++run) {
        Pair cur{2 * core.high, 4 * core.high - mod};
        if (run % 2) cur[run % 2] += Int(rng() % 33) - 16;
        int cost = core.score(cur, mod);
        for (int step = 0; step < 300; ++step) {
            auto x = cur;
            int i = rng() % 2;
            int kind = rng() % 5;
            Int sign = (rng() % 2) ? 1 : -1;
            if (kind <= 1) x[i] += sign * (1 + Int(rng() % 16));
            else if (kind == 2) x[i] += sign * power(rng() % (core.n - 1));
            else if (kind == 3) x[i] = Int(rng() % mod);
            else x[i] = sign * power(rng() % core.n) + Int(rng() % 9) - 4;
            for (auto& a : x) a = residue(a, mod);
            x[1] -= mod; // Fixed integer lifts used for the N* column.
            int next = core.score(x, mod);
            if (seen.insert(x).second) {
                ++proposals;
                if (next == 0) {
                    ++validCount;
                    std::cout << "candidate walk " << core.n << ' ' << mod << ' '
                              << x[0] << ' ' << x[1] << '\n';
                }
                if (next < best && !core.score(x, 0, 1)) { best = next; saved = x; }
            }
            int temperature = 1 + (299 - step) / 60;
            int delta = std::max(0, next - cost);
            int exponent = std::min(62, (delta + temperature - 1) / temperature);
            if ((rng() & ((std::uint64_t{1} << exponent) - 1)) == 0) {
                cur = x;
                cost = next;
            }
        }
    }
    if (best == std::numeric_limits<int>::max()) {
        saved = {2 * core.high, 4 * core.high - endpoint(core.n)};
        best = core.score(saved, mod);
        if (seen.insert(saved).second) {
            ++proposals;
            if (best == 0) {
                ++validCount;
                std::cout << "candidate fallback " << core.n << ' ' << mod << '\n';
            }
        }
    }
    return {saved, best};
}

// Exhaust both extra residues, pruning by validity of each one-point extension.
std::vector<Int> single_holes(int n, const BinaryCore& core) {
    const int d = n - 3;
    std::vector<Int> holes;
    for (int s = 0; s < n - 1; ++s) holes.push_back(s);
    // s=q*H+(H-1-mask). A single added point is absent from an
    // (n-1)-coin competitor exactly when s is tested with that budget.
    for (int q = 3; q <= 7; ++q) {
        auto generate = [&](auto&& self, int start, int budget, Int mask) -> void {
            holes.push_back((q + 1) * core.high - 1 - mask);
            if (budget == 0) return;
            for (int bit = start; bit < d; ++bit)
                self(self, bit + 1, budget - 1, mask | power(bit));
        };
        generate(generate, 0, q - 3, 0);
    }
    std::sort(holes.begin(), holes.end());
    return holes;
}

void exhaustive_pairs(int n) {
    BinaryCore core(n);
    int m = n - 2;
    auto holes = single_holes(n, core);
    if (n <= 12) {
        holes.resize(endpoint(n));
        std::iota(holes.begin(),holes.end(),Int{0});
    }
    Int universe = 0, pairs = 0, wins = 0;
    for (Int mod = power(n - 1); mod < endpoint(n); ++mod) {
        universe += (mod - m) * (mod - m - 1) / 2;
        std::vector<Int> eligible;
        for (Int w : holes) {
            if (w >= mod) break;
            Int x = residue(w - core.coreSum, mod);
            if (x > 0 && x <= core.high && (x & (x - 1)) == 0) continue;
            bool valid = true;
            for (int k = 0; k <= m + 1 && valid; ++k) {
                int slots = m + 1 - k;
                Int base = core.coreSum + (1 - k) * x;
                for (Int s = residue(base, mod); s <= slots * core.high; s += mod)
                    if (!(k == 1 && s == core.coreSum) && attainable(s, slots, core.high)) {
                        valid = false;
                        break;
                    }
            }
            if (valid) eligible.push_back(x);
        }
        for (std::size_t i = 0; i < eligible.size(); ++i) {
            for (std::size_t j = i + 1; j < eligible.size(); ++j) {
                ++pairs;
                if (!core.score({eligible[i], eligible[j]}, mod, 1)) {
                    ++wins;
                    std::cout << "candidate pair " << n << ' ' << mod << ' '
                              << eligible[i] << ' ' << eligible[j] << '\n';
                }
            }
        }
    }
    std::cout << "exhaustive " << n << ' ' << universe << ' ' << pairs << ' ' << wins << std::endl;
}

// All y below upper that cannot be made with exactly the given coin budget.
// Write y = q*H + (H-1-mask). Its greedy count is q+d-popcount(mask).
std::vector<Int> all_holes(int d, int coins, Int upper) {
    const Int high = power(d);
    std::vector<Int> holes;
    for (int y = 0; y < coins && y < upper; ++y) holes.push_back(y);
    for (int q = 0; q * high < upper; ++q) {
        int maxMissing = q + d - coins - 1;
        if (maxMissing < 0) continue;
        auto generate = [&](auto&& self, int start, int budget, Int mask) -> void {
            Int y = (q + 1) * high - 1 - mask;
            if (coins <= y && y < upper) holes.push_back(y);
            if (budget == 0) return;
            for (int i = start; i < d; ++i)
                self(self, i + 1, budget - 1, mask | power(i));
        };
        generate(generate, 0, maxMissing, 0);
    }
    std::sort(holes.begin(), holes.end());
    return holes;
}

bool single_valid(const BinaryCore& core, Int mod, Int x) {
    int size = core.n - 1;
    for (int k = 0; k <= size; ++k) {
        int slots = size - k;
        for (Int s = residue(core.coreSum + (1-k)*x, mod); s <= slots * core.high; s += mod)
            if (!(k == 1 && s == core.coreSum) && attainable(s, slots, core.high)) return false;
    }
    return true;
}

struct Census { Int pairs = 0, wins = 0; };

Census sparse_pairs(int n) {
    BinaryCore core(n);
    const Int low = power(n-1), end = endpoint(n), twiceSum = 2*core.coreSum;
    const auto omitted = all_holes(n-3, n-1, end + n);
    const auto doubled = all_holes(n-3, n-3, end);
    std::map<Int,std::vector<Int>> eligible;
    auto record = [&](Int mod, Int w) {
        Int x = residue(w - core.coreSum, mod);
        if (x > 0 && x <= core.high && (x & (x-1)) == 0) return;
        if (single_valid(core, mod, x)) eligible[mod].push_back(x);
    };
    for (Int w : omitted) {
        if (w >= end) break;
        if (w < n-1) {
            auto it = std::lower_bound(omitted.begin(), omitted.end(), low + w);
            for (; it != omitted.end() && *it < end + w; ++it) record(*it - w, w);
        } else {
            // Here w >= 4*H-1. Then (S-x) mod N = N + 2*S-w,
            // which must itself be a hole at the budget n-3.
            Int firstMod = std::max(low,w+1);
            auto it = std::lower_bound(doubled.begin(), doubled.end(), firstMod + twiceSum-w);
            for (; it != doubled.end() && *it < end + twiceSum-w; ++it)
                record(w + *it - twiceSum, w);
        }
    }
    Census result;
    for (const auto& [mod, xs] : eligible) {
        for (std::size_t i = 0; i < xs.size(); ++i)
            for (std::size_t j = 0; j < i; ++j) {
                ++result.pairs;
                if (!core.score({xs[i],xs[j]},mod,1)) {
                    ++result.wins;
                    std::cout << "candidate sparse " << n << ' ' << mod << ' '
                              << xs[i] << ' ' << xs[j] << std::endl;
                }
            }
    }
    std::cout << "sparse " << n << ' ' << eligible.size() << ' ' << result.pairs
              << ' ' << result.wins << std::endl;
    return result;
}

// Coordinate descent with all n residues movable. For each coordinate, build
// the full multiset coefficient table for the other n-1 once and score every
// replacement exactly. The walk changes a random coordinate at local minima.
void free_coordinates(int n) {
    std::mt19937_64 rng(8306600 + n);
    for (int mod : {int(endpoint(n) - 1), int(endpoint(n) - 2),
                    int(3 * power(n - 2) + 1)}) {
        int minimumRivals = std::numeric_limits<int>::max();
        std::uint64_t evaluations = 0;
        for (int run = 0; run < 4; ++run) {
            std::vector<int> a(n);
            std::vector<bool> used(mod);
            for (int i = 0; i < n; ++i) {
                int x = run < 2 ? int(power(i)) : int(rng() % mod);
                if (run == 1) x = (3 * x + int(rng() % 13)) % mod;
                while (used[x]) x = (x + 1) % mod;
                a[i] = x;
                used[x] = true;
            }
            for (int step = 0; step < 5 * n; ++step) {
                int i = (step + run) % n;
                used[a[i]] = false;
                int base = 0;
                std::vector<std::vector<int>> dp(n + 1, std::vector<int>(mod));
                dp[0][0] = 1;
                for (int j = 0; j < n; ++j) if (j != i) {
                    int x = a[j];
                    base += x;
                    for (int k = 1; k <= n; ++k) {
                        auto& curr = dp[k];
                        const auto& prev = dp[k - 1];
                        for (int t = x; t < mod; ++t) curr[t] += prev[t-x];
                        for (int t = 0; t < x; ++t) curr[t] += prev[t+mod-x];
                    }
                }
                int best = std::numeric_limits<int>::max();
                std::vector<int> tied;
                for (int x = 0; x < mod; ++x) if (!used[x]) {
                    int t = (base + x) % mod, rivals = -1;
                    for (int k = 0; k <= n; ++k) {
                        rivals += dp[n-k][t];
                        t -= x;
                        if (t < 0) t += mod;
                    }
                    ++evaluations;
                    if (!rivals) {
                        std::cout << "candidate free " << n << ' ' << mod;
                        for (int j = 0; j < n; ++j) std::cout << ' ' << (i == j ? x : a[j]);
                        std::cout << std::endl;
                        return;
                    }
                    if (rivals < best) { best = rivals; tied.clear(); }
                    if (rivals == best) tied.push_back(x);
                }
                minimumRivals = std::min(minimumRivals, best);
                int chosen = tied[rng() % tied.size()];
                if (step % (n + 1) == n) {
                    do { chosen = rng() % mod; } while (used[chosen]);
                }
                a[i] = chosen;
                used[chosen] = true;
            }
        }
        std::cout << "free " << n << ' ' << mod << ' ' << evaluations << ' '
                  << minimumRivals << std::endl;
    }
}

// Direct integer knapsack independently verifies least moduli for the first
// five finalists. Shifting the minimum to zero preserves the size constraint.
Int integer_table_minimum(const BinaryCore& core, Pair out) {
    std::vector<Int> values{out[0],out[1]};
    for (int i = 0; i < core.n-2; ++i) values.push_back(power(i));
    Int low = *std::min_element(values.begin(), values.end());
    Int sum = 0;
    for (Int& x : values) { x -= low; sum += x; }
    int limit = int(core.n * *std::max_element(values.begin(), values.end()));
    std::vector<std::vector<unsigned char>> dp(core.n+1, std::vector<unsigned char>(limit+1));
    dp[0][0] = 1;
    for (Int x : values)
        for (int k = 1; k <= core.n; ++k)
            for (int s = int(x); s <= limit; ++s)
                dp[k][s] = std::min(2, dp[k][s] + dp[k-1][s-x]);
    if (dp.back()[sum] != 1) return 0;
    for (int mod = 1; mod <= limit+1; ++mod) {
        int count = 0;
        for (int s = sum % mod; s <= limit && count < 2; s += mod) count += dp.back()[s];
        if (count == 1) return mod;
    }
    throw std::logic_error("no minimum in integer-table range");
}

int main(int argc, char** argv) {
    if (argc == 2 && std::string(argv[1]) == "--sparse") {
        for (int n = 8; n <= 25; ++n) sparse_pairs(n);
        return 0;
    }
    if (argc == 2 && std::string(argv[1]) == "--free") {
        for (int n = 8; n <= 12; ++n) free_coordinates(n);
        return 0;
    }
    if (argc == 2 && std::string(argv[1]) == "--pairs") {
        for (int n = 8; n <= 18; ++n) exhaustive_pairs(n);
        return 0;
    }
    controls();
    progression_controls();
    classical_integer_tests();
    for (int n = 8; n <= 25; ++n) {
        greedy_test(n);
        doubled_core(n);
        quadrupled_core(n);
        BinaryCore core(n);
        std::mt19937_64 rng(260708366 + n);
        int proposals = 0, valid = 0;
        AnnealingResult finalist{};
        for (Int mod : {endpoint(n) - 1, endpoint(n) - 3,
                         power(n) - power(n / 2), 3 * power(n - 2) - 1}) {
            auto result = anneal(core, mod, rng, proposals, valid);
            if (mod == endpoint(n) - 1) finalist = result;
        }
        auto least = core.minimum(finalist.out);
        if (n <= 12 && integer_table_minimum(core, finalist.out) != least)
            throw std::logic_error("independent integer-table minimum disagrees");
        std::cout << "walk " << n << ' ' << proposals << ' ' << valid << ' '
                  << finalist.out[0] << ' ' << finalist.out[1] << ' '
                  << finalist.score << ' ' << least << std::endl;
    }
}
