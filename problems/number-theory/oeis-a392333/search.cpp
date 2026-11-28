#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <unordered_map>
#include <vector>

using Signature = std::uint64_t;

// This linear projection is used only to reject impossible parity vectors.
// Every match is checked in all prime coordinates by Legendre's formula.
Signature prime_signature(Signature p) {
    p += UINT64_C(0x9e3779b97f4a7c15);
    p = (p ^ (p >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    p = (p ^ (p >> 27)) * UINT64_C(0x94d049bb133111eb);
    return p ^ (p >> 31);
}

struct Tables {
    std::vector<int> smallest_factor, preceding_prime, primes;
    std::vector<Signature> factorial_signature;
    std::unordered_map<Signature, std::vector<int>> occurrences;

    explicit Tables(int limit) : smallest_factor(limit + 1), preceding_prime(limit + 1),
                                 factorial_signature(limit + 1) {
        for (int p = 2; p <= limit; ++p) {
            if (smallest_factor[p] != 0) continue;
            primes.push_back(p);
            for (int j = p; j <= limit; j += p) {
                if (smallest_factor[j] == 0) smallest_factor[j] = p;
            }
        }
        for (int n = 1; n <= limit; ++n) {
            preceding_prime[n] = smallest_factor[n] == n ? n : preceding_prime[n - 1];
            Signature s = factorial_signature[n - 1];
            for (int v = n; v > 1; v /= smallest_factor[v]) s ^= prime_signature(smallest_factor[v]);
            factorial_signature[n] = s;
            occurrences[s].push_back(n);
        }
    }
};

bool is_remaining_candidate(int n, const Tables& tables) {
    int count = 0;
    while (n > 1) {
        const int p = tables.smallest_factor[n];
        n /= p;
        if (p < 13 || n % p == 0) return false;
        ++count;
    }
    return count >= 4;
}

bool is_square_product(const std::vector<int>& indices, const Tables& tables) {
    for (int p : tables.primes) {
        if (p > indices.back()) break;
        int parity = 0;
        for (int n : indices) {
            while (n >= p) {
                n /= p;
                parity ^= n % 2;
            }
        }
        if (parity) return false;
    }
    return true;
}

std::vector<int> find_representation(int e, const Tables& tables, std::uint64_t& pairs) {
    const auto& signature = tables.factorial_signature;
    std::set<int> target_primes;
    for (int d = e - 1; d >= tables.preceding_prime[e]; --d) {
        // target_primes is the squarefree kernel of e!/d!.
        for (int v = d + 1; v > 1; v /= tables.smallest_factor[v]) {
            const int p = tables.smallest_factor[v];
            if (!target_primes.erase(p)) target_primes.insert(p);
        }
        const int q = target_primes.empty() ? 1 : *target_primes.rbegin();
        for (int c = std::max(3, q); c < d; ++c) {
            const int last = tables.preceding_prime[c];
            const int first_b = last > q ? last : 2;
            for (int b = first_b; b < c; ++b) {
                ++pairs;
                const Signature wanted = signature[b] ^ signature[c] ^ signature[d] ^ signature[e];
                auto it = tables.occurrences.find(wanted);
                if (it == tables.occurrences.end()) continue;
                for (int a : it->second) {
                    if (a >= b) break;
                    std::vector<int> witness{a, b, c, d, e};
                    if (is_square_product(witness, tables)) return witness;
                }
            }
        }
    }
    return {};
}

int main() {
    constexpr int upper_bound = 435643;
    Tables tables(upper_bound);
    int candidates = 0;
    std::cout << "a,b,c,d,e\n";
    for (int e = 7; e <= upper_bound; ++e) {
        if (!is_remaining_candidate(e, tables)) continue;
        ++candidates;
        std::uint64_t pairs = 0;
        auto witness = find_representation(e, tables, pairs);
        if (witness.empty()) {
            std::cerr << "First excluded endpoint: " << e << "; earlier witnesses: " << candidates - 1
                      << "; final triples (b,c,d) checked: " << pairs << '\n';
            return e == upper_bound ? EXIT_SUCCESS : EXIT_FAILURE;
        }
        for (std::size_t j = 0; j < witness.size(); ++j)
            std::cout << (j ? "," : "") << witness[j];
        std::cout << '\n';
    }
    std::cerr << "No excluded endpoint through " << upper_bound << '\n';
    return EXIT_FAILURE;
}
