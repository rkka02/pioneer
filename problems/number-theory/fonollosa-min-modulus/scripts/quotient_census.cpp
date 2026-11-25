// Exhaustive nine-element quotient census at 504, 505, 506 and 507.
// Each branch contains zero, so the bitsets for exactly k terms include
// the sums attained with fewer terms by padding with zero.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <vector>

namespace {
constexpr int size = 9, words = 8;
using Word = std::uint64_t;
using Bits = std::array<Word, words>;
using Sums = std::array<Bits, size + 1>;

class Census {
    int mod, gcdMin = 1;
    std::array<int,512> inverse{};
    std::array<int,size> points{};
    std::array<Word,size+1> nodes{};
    int validForms = 0;

    static bool has(const Bits& bits, int x) {
        return (bits[x / 64] >> (x % 64)) & 1;
    }

    Sums with_zero() const {
        Sums sums{};
        for (auto& row : sums) row[0] = 1;
        return sums;
    }

    // R_k(B+x) = R_k(B) union (x + R_{k-1}(B+x)). Shift modulo mod by
    // concatenating two copies of the packed child row and taking a window.
    void adjoin(Sums& child, const Sums& parent, int x) const {
        child[0] = parent[0];
        int word = (mod-x)/64, offset = (mod-x)%64;
        int tail = mod%64, slack = 64-tail;
        for (int k = 1; k <= size; ++k) {
            const auto& b = child[k-1];
            std::array<Word,2*words> buffer;
            for (int i = 0; i < words-1; ++i) buffer[i] = b[i];
            buffer[words-1] = b[words-1] | (b[0] << tail);
            for (int i = 0; i < words-1; ++i)
                buffer[words+i] = (b[i] >> slack) | (b[i+1] << tail);
            buffer[2*words-1] = b[words-1] >> slack;
            for (int i = 0; i < words; ++i) {
                Word shifted = buffer[word+i] >> offset;
                if (offset) shifted |= buffer[word+i+1] << (64-offset);
                child[k][i] = parent[k][i] | shifted;
            }
            child[k][words-1] &= (Word{1} << tail)-1;
        }
    }

    bool permits(const Sums& sums, int k, int sum, int x) const {
        int target = sum + x;
        if (target >= mod) target -= mod;
        if (has(sums[k+1], target)) return false;
        target = sum;
        for (int h = 2; h <= k+1; ++h) {
            target -= x;
            if (target < 0) target += mod;
            if (has(sums[k+1-h], target)) return false;
        }
        return true;
    }

    // A lexicographically smaller normalized partial subset also gives a
    // smaller prefix for the transformed completion. This extra pruning is
    // used only for gcdMin == 1, where the affine multiplier is unique.
    bool canonical(int k) const {
        if (gcdMin != 1) return true;
        for (int i = 0; i < k; ++i) for (int j = 0; j < k; ++j) {
            int u = inverse[(points[j]-points[i]+mod)%mod];
            if (!u || (i == 0 && j == 1)) continue;
            auto transformed = [&](int z) { return (points[z]-points[i]+mod)*u%mod; };
            int third = mod;
            for (int z = 0; z < k; ++z) if (z != i && z != j)
                third = std::min(third,transformed(z));
            if (third < points[2]) return false;
            if (third > points[2] || k == 3) continue;
            std::array<int,size> sorted{};
            for (int z = 0; z < k; ++z) sorted[z] = transformed(z);
            std::sort(sorted.begin(), sorted.begin()+k);
            if (std::lexicographical_compare(sorted.begin(),sorted.begin()+k,
                                             points.begin(),points.begin()+k)) return false;
        }
        return true;
    }

    void search(const Sums& sums, int k, int sum) {
        ++nodes[k];
        for (int word = 0; word < words; ++word) {
            Word missing = ~sums[k+1][word];
            while (missing) {
                int w = 64*word + __builtin_ctzll(missing);
                missing &= missing-1;
                if (w >= mod) continue;
                int x = w-sum;
                if (x < 0) x += mod;
                if (x <= points[k-1] || x > mod-(size-k)) continue;
                if (gcdMin > 1 && std::any_of(points.begin(),points.begin()+k,
                        [&](int y) { return std::gcd(x-y,mod) < gcdMin; })) continue;
                if (!permits(sums,k,sum,x)) continue;
                points[k] = x;
                if (!canonical(k+1)) continue;
                if (k+1 == size) {
                    if (!direct_valid()) throw std::logic_error("leaf count disagrees");
                    ++validForms;
                    std::cout << "FOUND " << mod;
                    for (int z : points) std::cout << ' ' << z;
                    std::cout << std::endl;
                } else {
                    Sums next;
                    adjoin(next,sums,x);
                    search(next,k+1,(sum+x)%mod);
                }
            }
        }
    }

    bool direct_valid() const {
        std::vector<std::vector<int>> dp(size+1,std::vector<int>(mod));
        dp[0][0] = 1;
        int sum = 0;
        for (int x : points) {
            sum += x;
            for (int k = 1; k <= size; ++k)
                for (int s = 0; s < mod; ++s) dp[k][(s+x)%mod] += dp[k-1][s];
        }
        return dp[size][sum%mod] == 1;
    }

    // Exercise wrap positions against scalar, cyclic reachability rows.
    void check_shifts() const {
        std::mt19937_64 rng(260708366);
        for (int x = 1; x < mod; ++x) {
            Sums parent{}, child;
            for (auto& row : parent) {
                for (auto& word : row) word = rng();
                row.back() &= (Word{1} << (mod%64))-1;
            }
            adjoin(child,parent,x);
            for (int k = 1; k <= size; ++k)
                for (int s = 0; s < mod; ++s)
                    if (has(child[k],s) !=
                        (has(parent[k],s) || has(child[k-1],(s-x+mod)%mod)))
                        throw std::logic_error("cyclic shift check failed");
        }
    }

public:
    explicit Census(int modulus) : mod(modulus) {
        for (int i = 1; i < mod; ++i) for (int j = 1; j < mod; ++j)
            if (i*j%mod == 1) inverse[i] = j;
    }

    void run() {
        check_shifts();
        const Sums zero = with_zero();
        points[0] = 0;
        for (gcdMin = 1; gcdMin < mod; ++gcdMin) if (mod % gcdMin == 0) {
            points[1] = gcdMin;
            Sums start;
            adjoin(start,zero,gcdMin);
            search(start,2,gcdMin);
        }
        std::cout << "done " << mod << " valid forms " << validForms << " nodes";
        for (int k = 2; k < size; ++k) std::cout << ' ' << nodes[k];
        std::cout << std::endl;
    }
};
} // namespace

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    int mod = std::atoi(argv[1]);
    if (mod < 504 || mod > 507) return 2;
    Census(mod).run();
}
