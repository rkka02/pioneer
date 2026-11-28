#include <algorithm>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>

namespace {
constexpr int endpoint = 435643;
constexpr int coordinates = 64;
using Mask = std::uint64_t;

std::vector<int> primes_up_to(int n) {
    std::vector<bool> composite(n + 1);
    std::vector<int> primes;
    for (int p = 2; p <= n; ++p) {
        if (composite[p]) continue;
        primes.push_back(p);
        if (p <= n / p) {
            for (int m = p * p; m <= n; m += p) composite[m] = true;
        }
    }
    return primes;
}

int factorial_parity(int n, int p) {
    int parity = 0;
    while (n >= p) {
        n /= p;
        parity ^= n % 2;
    }
    return parity;
}

struct Witness {
    int a, b, c, d, e;
};

bool ordered(Witness w) {
    return 0 < w.a && w.a < w.b && w.b < w.c && w.c < w.d && w.d < w.e;
}

bool exact(Witness w, const std::vector<int>& primes) {
    if (!ordered(w)) return false;
    for (int p : primes) {
        if (p > w.e) break;
        if (factorial_parity(w.a, p) ^ factorial_parity(w.b, p) ^
            factorial_parity(w.c, p) ^ factorial_parity(w.d, p) ^
            factorial_parity(w.e, p)) return false;
    }
    return true;
}

struct Factorization {
    int multiplicity = 0;
    int smallest = 0;
    int repeated = 0;
};

Factorization factor(int n, const std::vector<int>& primes) {
    Factorization info;
    for (int p : primes) {
        if (p > n / p) break;
        if (n % p != 0) continue;
        if (info.smallest == 0) info.smallest = p;
        int exponent = 0;
        do {
            n /= p;
            ++exponent;
        } while (n % p == 0);
        info.multiplicity += exponent;
        if (exponent >= 2) info.repeated = p;
    }
    if (n > 1) {
        ++info.multiplicity;
        if (info.smallest == 0) info.smallest = n;
    }
    return info;
}

// The adjacent factorial pairs contribute the squarefree parts of m and e.
// If e = p*m, and t! has squarefree part p*q, use q*m in place of m.
Witness easy_witness(int e, Factorization info) {
    struct Identity { int p, q, t; };
    constexpr Identity identities[] = {{2, 1, 2}, {3, 2, 3}, {5, 1, 6},
                                      {7, 5, 7}, {11, 7, 11}};
    for (auto [p, q, t] : identities) {
        if (info.smallest == p) {
            const int m = q * (e / p);
            return {t, m - 1, m, e - 1, e};
        }
    }
    if (info.repeated != 0) {
        const int m = e / info.repeated / info.repeated;
        return {1, m - 1, m, e - 1, e};
    }
    return {};
}

// For every x, this is an exact 64-coordinate projection, not a hash of
// the complete parity vector. A zero projected sum is only a candidate.
class Search {
public:
    explicit Search(const std::vector<int>& primes)
        : primes_(primes), profiles_(endpoint + 1), greatest_prime_(endpoint + 1) {
        if (primes_.size() < coordinates) throw std::runtime_error("Too few primes");
        indices_.reserve(endpoint);
        int prime_index = 0;
        for (int x = 1; x <= endpoint; ++x) {
            while (primes_[prime_index] <= x &&
                   prime_index + 1 < static_cast<int>(primes_.size())) ++prime_index;
            greatest_prime_[x] = primes_[prime_index] <= x ? primes_[prime_index]
                              : prime_index == 0 ? 0 : primes_[prime_index - 1];
            for (int j = 0; j < coordinates; ++j) {
                profiles_[x] |= Mask(factorial_parity(x, primes_[j])) << j;
            }
            indices_[profiles_[x]].push_back(x);
        }
    }

    Witness find(int e, bool log) const {
        int largest_prime = greatest_prime_[e];
        if (!(e / 2 < largest_prime && largest_prime < e)) {
            throw std::runtime_error("Invalid largest-prime cutoff");
        }
        for (int d = e - 1; d >= largest_prime; --d) {
            int q = largest_suffix_prime(d, e);
            std::uint64_t tested_bc = 0;
            std::uint64_t projected_hits = 0;
            for (int c = std::max(3, q); c < d; ++c) {
                const int p = greatest_prime_[c];
                int lower_b = 2;
                // If the suffix does not touch p in odd parity and c!
                // touches p in odd parity, at least b! must touch p.
                if (q < p && factorial_parity(c, p) != 0) lower_b = p;
                const Mask remaining = profiles_[c] ^ profiles_[d] ^ profiles_[e];
                for (int b = lower_b; b < c; ++b) {
                    ++tested_bc;
                    auto it = indices_.find(remaining ^ profiles_[b]);
                    if (it == indices_.end()) continue;
                    for (int a : it->second) {
                        if (a >= b) break;
                        ++projected_hits;
                        Witness w{a, b, c, d, e};
                        if (exact(w, primes_)) return w;
                    }
                }
            }
            if (log) std::cerr << "d=" << d << " greatest odd suffix prime=" << q
                               << " (b,c) candidates=" << tested_bc
                               << " projected tuples=" << projected_hits << '\n';
        }
        return {};
    }

    void verify_other_lengths() const {
        const int P = greatest_prime_[endpoint];
        if (endpoint >= 2 * P || factorial_parity(endpoint, P) != 1) {
            throw std::runtime_error("One-factor obstruction failed");
        }
        // A prime above e/2 contributes once to e!, so the preceding index
        // in any two- or three-factor witness must be at least P.
        for (int d = P; d < endpoint; ++d) {
            const int q = largest_suffix_prime(d, endpoint);
            if (q == 1) throw std::runtime_error("Found a two-factor witness");
            for (int a = q; a < d; ++a) {
                const int p = greatest_prime_[a];
                if (p > q && factorial_parity(a, p) != 0) continue;
                auto stop = std::find_if(primes_.begin(), primes_.end(), [&](int r) {
                    return factorial_parity(a, r) ^ factorial_parity(d, r) ^
                           factorial_parity(endpoint, r);
                });
                if (stop == primes_.end()) throw std::runtime_error("Found a three-factor witness");
                std::cerr << "three-factor obstruction: a=" << a << " d=" << d
                          << " p=" << *stop << '\n';
            }
        }
        // Any four-factor witness either contains 1! and reduces to three,
        // or can be extended to five by inserting 1!.
        constexpr int first = 13;
        constexpr int second = 33511;
        if (!(1 < first && first < second - 1 && second < endpoint - 1 &&
              first * second == endpoint)) {
            throw std::runtime_error("Six-factor identity failed");
        }
        for (int p : primes_) {
            if (factorial_parity(first - 1, p) ^ factorial_parity(first, p) ^
                factorial_parity(second - 1, p) ^ factorial_parity(second, p) ^
                factorial_parity(endpoint - 1, p) ^ factorial_parity(endpoint, p)) {
                throw std::runtime_error("Six-factor valuation check failed");
            }
        }
        std::cerr << "Minimum number of factorials at " << endpoint << ": 6\n";
    }

private:
    int largest_suffix_prime(int d, int e) const {
        auto it = std::upper_bound(primes_.begin(), primes_.end(), e);
        while (it != primes_.begin()) {
            int p = *--it;
            if (factorial_parity(d, p) != factorial_parity(e, p)) return p;
        }
        return 1;
    }

    const std::vector<int>& primes_;
    std::vector<Mask> profiles_;
    std::vector<int> greatest_prime_;
    std::unordered_map<Mask, std::vector<int>> indices_;
};

bool check_easy_witness(Witness w, Factorization info, const std::vector<int>& primes) {
    if (!ordered(w) || w.b + 1 != w.c || w.d + 1 != w.e) return false;
    if (info.smallest > 11) {
        return w.a == 1 && info.repeated > 1 &&
               1LL * w.c * info.repeated * info.repeated == w.e;
    }
    // The product is a square iff a! * c * e is a square. It suffices to
    // check the primes up to a and the common factor stripped from c and e.
    const int m = w.e / info.smallest;
    if (w.c % m != 0) return false;
    const int p = info.smallest;
    const int q = w.c / m;
    for (int r : primes) {
        if (r > std::max({w.a, p, q})) break;
        if (factorial_parity(w.a, r) ^ int(p == r) ^ int(q == r)) return false;
    }
    return std::binary_search(primes.begin(), primes.end(), p) &&
           (q == 1 || std::binary_search(primes.begin(), primes.end(), q));
}
}  // namespace

int main() {
    const auto primes = primes_up_to(endpoint);
    const Search search(primes);
    int easy = 0;
    int nontrivial = 0;
    std::cout << "e,a,b,c,d\n";
    for (int e = 2; e <= endpoint; ++e) {
        auto info = factor(e, primes);
        if (info.multiplicity < 4) continue;
        auto simple = easy_witness(e, info);
        if (simple.e != 0) {
            if (!check_easy_witness(simple, info, primes) || e == endpoint) {
                throw std::runtime_error("Unexpected elementary witness at " + std::to_string(e));
            }
            ++easy;
            continue;
        }
        auto w = search.find(e, e == endpoint);
        if (e == endpoint) {
            if (w.e != 0 || info.multiplicity != 4 || e != 13 * 23 * 31 * 47) {
                throw std::runtime_error("Endpoint check failed");
            }
            search.verify_other_lengths();
            std::cerr << "Verified least excluded endpoint: " << endpoint << '\n'
                      << "Earlier elementary witnesses: " << easy << '\n'
                      << "Earlier nontrivial exact witnesses: " << nontrivial << '\n';
            return 0;
        }
        if (!ordered(w)) throw std::runtime_error("Earlier exclusion at " + std::to_string(e));
        ++nontrivial;
        std::cout << w.e << ',' << w.a << ',' << w.b << ',' << w.c << ',' << w.d << '\n';
    }
    throw std::runtime_error("Did not reach the expected endpoint");
}
