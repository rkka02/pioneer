#pragma once

#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <numeric>
#include <stdexcept>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

using Word = std::uint64_t;
using Bits = std::array<Word,16>;
using Rows = std::array<Bits,11>;
using Points = std::array<int,10>;
using Counts = std::array<std::uint64_t,12>;
constexpr int target = 10;

struct Modulus {
    int n, words;
    Word last;
    std::vector<int> gcds, inverses;
    std::vector<std::vector<int>> coord;
    std::vector<unsigned char> admissible;
    std::vector<unsigned short> tripleMin;
    std::vector<unsigned short> outsideMin2;
    std::vector<int> seed;
    bool reductions, nineEvenPossible=true;

    Modulus(int modulus, bool restricted) : n(modulus), words((n+63)/64),
        last(n%64 ? (Word{1}<<(n%64))-1 : ~Word{0}), gcds(n), inverses(n),
        coord(n), admissible(n,1), reductions(restricted) {
        for (int d=0; d<n; ++d) gcds[d]=std::gcd(d,n);
        for (int d=1; d<n; ++d) {
            const int g=gcds[d], order=n/g;
            for (int j=1; j<n && g==1; ++j) if (j*d%n==1) { inverses[d]=j; break; }
            coord[d].resize(n);
            for (int s=0; s<g; ++s) {
                int x=s;
                for (int t=0; t<order; ++t) { coord[d][x]=s*order+t; x=add(x,d); }
            }
            if (reductions && ((order==2 && n<1016) || (order==3 && n<768)))
                admissible[d]=0;
        }
        tripleMin.assign(n*n,n);
        for (int u=1;u<n;++u) for (int v=u+1;v<n;++v) {
            int x[3]={0,u,v}, best=n;
            for (int i=0;i<3;++i) for (int j=0;j<3;++j) if (i!=j) {
                int inv=inverses[sub(x[j],x[i])];
                if (inv) best=std::min(best,sub(x[3-i-j],x[i])*inv%n);
            }
            tripleMin[n*u+v]=best;
        }
        if (n==1008) {
            // At subgroup order 504 the only nine-set orbit is binary.
            nineEvenPossible=false;
            for (int y=1;y<n;y+=2) {
                bool hasUnit=false;
                for (int i=0;i<9;++i) hasUnit |= gcds[sub(y,2*((1<<i)-1))]==1;
                nineEvenPossible |= !hasUnit;
            }
        }
    }

    void prepareNonunits() {
        if (n%2) return;
        std::vector<unsigned short> first(n*n,n);
        for (int d=1;d<n;++d) if (gcds[d]==2) {
            for (int unit=1;unit<n;++unit) if (gcds[unit]==1 && unit*d%n==2) {
                for (int z=1;z<n;z+=2) {
                    auto& entry=first[n*d+z];
                    entry=std::min<int>(entry,unit*z%n);
                }
            }
        }
        outsideMin2.assign(n*n,n);
        for (int u=1;u<n;++u) for (int v=u+1;v<n;++v) {
            outsideMin2[n*u+v]=std::min({first[n*u+v],first[n*v+u],
                first[n*sub(0,u)+sub(v,u)],first[n*sub(v,u)+sub(0,u)],
                first[n*sub(0,v)+sub(u,v)],first[n*sub(u,v)+sub(0,v)]});
        }
    }

    int add(int x,int y) const { int v=x+y; return v>=n ? v-n : v; }
    int sub(int x,int y) const { int v=x-y; return v<0 ? v+n : v; }
    bool has(const Bits& b,int x) const { return (b[x/64]>>(x%64))&1; }
    void set(Bits& b,int x) const { b[x/64] |= Word{1}<<(x%64); }

    // Rotate a cyclic bit string of n bits, then take the union with old.
    void shiftedUnion(Bits& dest,const Bits& b,const Bits& old,int x) const {
        const int lw=x/64, lb=x%64, rw=(n-x)/64, rb=(n-x)%64;
        for (int i=0; i<words; ++i) {
            Word v=old[i];
            if (i>=lw) v |= b[i-lw]<<lb;
            if (lb && i>lw) v |= b[i-lw-1]>>(64-lb);
            if (i+rw<words) v |= b[i+rw]>>rb;
            if (rb && i+rw+1<words) v |= b[i+rw+1]<<(64-rb);
            dest[i]=v;
        }
        dest[words-1]&=last;
    }
    void adjoin(Rows& next,const Rows& old,int x) const {
        next[0]=old[0];
        for (int k=1;k<=target;++k) shiftedUnion(next[k],next[k-1],old[k],x);
    }
    bool permits(const Rows& old,int k,int sum,int x) const {
        if (has(old[k+1],add(sum,x))) return false;
        int v=sum;
        for (int h=2;h<=k+1;++h) {
            v=sub(v,x);
            if (has(old[k+1-h],v)) return false;
        }
        return true;
    }
    bool missingTarget(const Rows& old) const {
        for (int i=0;i<words;++i) if (old[10][i]!=(i+1==words?last:~Word{0})) return true;
        return false;
    }

    // A direct count from the frozen definition, independent of insertion.
    bool direct(const Points& a) const {
        std::vector<std::vector<unsigned>> dp(11,std::vector<unsigned>(n));
        dp[0][0]=1;
        int total=0;
        for (int x:a) {
            total=add(total,x);
            for (int k=1;k<=10;++k)
                for (int s=0;s<n;++s) dp[k][add(s,x)]+=dp[k-1][s];
        }
        return dp[10][total]==1;
    }
    void check() const {
        Bits old{}, b{}, got{};
        for (int z=0;z<n;++z) {
            if ((z*z+13*z+1)%19<4) set(old,z);
            if ((z*7+3)%23<5) set(b,z);
        }
        for (int x=0;x<n;++x) {
            shiftedUnion(got,b,old,x);
            for (int z=0;z<n;++z) if (has(got,z)!=(has(old,z)||has(b,sub(z,x))))
                throw std::logic_error("bit rotation");
        }
    }
};

