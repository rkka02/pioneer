// Exact ten-set search. A shard fixes the least pairwise gcd and the third
// residue of a sorted affine normalization. No search budget truncates a shard.
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

struct Search {
    const Modulus& m;
    int g, third;
    Points a{};
    Counts counts{};
    std::vector<Points> leaves;
    bool outsideMode=false;

    bool tripleOk(int a,int b,int c) const {
        if (g==1) return m.tripleMin[(b-a)*m.n+c-a]>=third;
        if (!outsideMode || g!=2 || m.outsideMin2.empty()) return true;
        const int lo=std::min({a,b,c}), hi=std::max({a,b,c}), mid=a+b+c-lo-hi;
        return m.outsideMin2[(mid-lo)*m.n+hi-lo]>=third;
    }
    bool compatible(int k,int x) const {
        for (int i=0;i<k;++i) {
            int diff=std::abs(x-a[i]);
            if (!m.admissible[diff] || m.gcds[diff]<g) return false;
            for (int j=0;j<i;++j) if (!tripleOk(a[j],a[i],x)) return false;
        }
        return true;
    }
    // The capacity is computed in steps of b-a, with signed rank increases.
    bool capacity(int k,int i,int j) const {
        int d=m.sub(a[j],a[i]), order=m.n/m.gcds[d];
        std::array<int,256> positions{}, ranks{};
        int used=1;
        for (int h=0;h<k;++h) if (h!=i && h!=j) {
            int x=m.sub(a[h],a[i]);
            for (int z=0;z<used;++z) {
                positions[z+used]=m.add(positions[z],x);
                ranks[z+used]=ranks[z]+1;
            }
            used*=2;
        }
        for (int z=0;z<used;++z) positions[z]=16*m.coord[d][positions[z]]+ranks[z];
        std::sort(positions.begin(),positions.begin()+used);
        int cap=m.gcds[d]*(order/2);
        for (int begin=0;begin<used;) {
            int end=begin+1, group=(positions[begin]/16)/order;
            while (end<used && (positions[end]/16)/order==group) ++end;
            cap-=order/2;
            for (int z=begin;z<end;++z) {
                int next=(z+1==end?begin:z+1);
                int gap=positions[next]/16-positions[z]/16+(next==begin?order:0);
                int inc=std::max(0,(positions[next]%16)-(positions[z]%16));
                if (gap<2+inc) return false;
                cap+=(gap-inc)/2;
            }
            begin=end;
        }
        return cap>=256;
    }
    bool caps(int k) const {
        // A subset of the available pivot checks suffices for a sound cut.
        if (m.n>700 && k<8) return true;
        for (int i=0;i<k;++i) for (int j=i+1;j<k;++j) {
            if (m.n>700 && i>0 && m.gcds[m.sub(a[j],a[i])]<16) continue;
            if (!capacity(k,i,j)) return false;
        }
        return true;
    }
    void accept() {
        if (!m.direct(a)) throw std::logic_error("invalid leaf");
        ++counts[10]; leaves.push_back(a);
    }
    void dfs(const Rows& rows,int k,int sum,const std::vector<int>& possible) {
        ++counts[k];
        if (!m.missingTarget(rows)) { ++counts[0]; return; }
        if (k>=5 && !caps(k)) { ++counts[1]; return; }
        std::vector<int> eligible;
        for (int x:possible) if (m.permits(rows,k,sum,x)) eligible.push_back(x);
        if (int(eligible.size())<10-k) return;
        if (g>1 && m.n<1024) {
            int divisor=g;
            for(int i=2;i<k;++i) divisor=std::gcd(divisor,a[i]);
            for(int y:eligible) { if(divisor==1) break; divisor=std::gcd(divisor,y); }
            if(divisor>1) { ++counts[11]; return; }
        }
        if (k==8) {
            std::vector<unsigned char> allowed(m.n);
            for (int x:eligible) allowed[x]=1;
            for (int t=0;t<m.words;++t) {
                Word holes=~rows[10][t] & (t+1==m.words?m.last:~Word{0});
                while (holes) {
                    int p=64*t+__builtin_ctzll(holes); holes&=holes-1;
                    int pair=m.sub(p,sum);
                    for (int x:eligible) {
                        int y=m.sub(pair,x);
                        if (y<=x || !allowed[y]) continue;
                        a[8]=x;
                        if (!compatible(9,y)) continue;
                        Rows extended;
                        m.adjoin(extended,rows,x);
                        if (m.permits(extended,9,m.add(sum,x),y)) { a[9]=y; accept(); }
                    }
                }
            }
            return;
        }
        for (std::size_t i=0;i+10-k<=eligible.size();++i) {
            int x=eligible[i]; a[k]=x;
            std::vector<int> rest;
            for (std::size_t j=i+1;j<eligible.size();++j) {
                int y=eligible[j];
                if (!m.admissible[y-x] || m.gcds[y-x]<g) continue;
                bool ok=true;
                for (int h=0;h<k && ok;++h) ok=tripleOk(a[h],x,y);
                if (ok) rest.push_back(y);
            }
            if (int(rest.size())<9-k) continue;
            Rows next; m.adjoin(next,rows,x);
            dfs(next,k+1,m.add(sum,x),rest);
        }
    }
    void run(bool nonunitWitness) {
        outsideMode=nonunitWitness;
        if (g>=third || (!nonunitWitness && third>m.n-8) || !m.admissible[g]) return;
        int p=2;
        if (nonunitWitness) {
            while (g%p!=0) ++p;
            if (third%p==0) return;
        }
        a[0]=0; a[1]=g;
        Rows zero{}, two{}, three{};
        for (auto& row:zero) row[0]=1;
        m.adjoin(two,zero,g);
        if (!compatible(2,third) || !m.permits(two,2,g,third)) return;
        a[2]=third;
        m.adjoin(three,two,third);
        int depth=3, sum=m.add(g,third);
        for (int x:m.seed) {
            if (x<=a[depth-1] || x>=m.n || !compatible(depth,x) || !m.permits(three,depth,sum,x)) return;
            a[depth++]=x;
            Rows next{}; m.adjoin(next,three,x); three=next;
            sum=m.add(sum,x);
        }
        std::vector<int> cand;
        if (nonunitWitness) {
            // A generating set contains a first residue off the subgroup pZ.
            // Fix it before the sorted search of the remaining coordinates.
            for (int x=g+1;x<m.n;++x)
                if ((x>third || (x<third && x%p==0)) && compatible(depth,x)) cand.push_back(x);
            // A nine-set in the subgroup requires order at least 504. The
            // Round 1 nine-set census also excludes orders 505, 506 and 507.
            const int quotient=m.n/p;
            if (quotient<504 || (505<=quotient && quotient<=507) || (p==2 && !m.nineEvenPossible)) {
                for (int y:cand) {
                    if (y%p==0 || !m.permits(three,depth,sum,y)) continue;
                    a[depth]=y;
                    std::vector<int> remaining;
                    for (int x:cand) {
                        int gap=std::abs(x-y);
                        if ((x>y || (x<y && x%p==0)) && m.admissible[gap] && m.gcds[gap]>=g) {
                            bool ok=true;
                            for (int i=0;i<depth && ok;++i) ok=tripleOk(a[i],y,x);
                            if (ok) remaining.push_back(x);
                        }
                    }
                    if (int(remaining.size())<9-depth) continue;
                    Rows extended;
                    m.adjoin(extended,three,y);
                    dfs(extended,depth+1,m.add(sum,y),remaining);
                }
                return;
            }
        } else {
            for (int x=a[depth-1]+1;x<m.n;++x) if (compatible(depth,x)) cand.push_back(x);
        }
        dfs(three,depth,sum,cand);
    }
};

int main(int argc,char** argv) {
    if (argc<6 || argc>8) {
        std::cerr<<"usage: round2_ten N gcd-filter first-third last-third threads [raw|standard] [comma-separated seed after third]\n"
                 <<"gcd-filter: 0 for all, -1 for all nonunits, or a positive least pairwise gcd\n";
        return 2;
    }
    int n=std::stoi(argv[1]), only=std::stoi(argv[2]), lo=std::stoi(argv[3]);
    int hi=std::stoi(argv[4]), threads=std::stoi(argv[5]);
    if (n<512 || n>1024 || lo<2 || hi<lo || threads<1 || only < -1) return 2;
    Modulus m(n,argc==6 || std::string(argv[6])=="standard"); m.check();
    if (argc==8) {
        if (lo!=hi || only<=0) return 2;
        std::stringstream ss(argv[7]); std::string part;
        while (std::getline(ss,part,',')) m.seed.push_back(std::stoi(part));
        if (m.seed.size()>5) return 2;
    }
    int distinctPrimes=0, residual=n;
    for(int p=2;p<=residual;++p) if(residual%p==0){
        ++distinctPrimes; while(residual%p==0) residual/=p;
    }
    const bool nonunitWitness = only == -1 && n<1024 && lo==2 && hi>=n-1;
    if (nonunitWitness && distinctPrimes>=3) m.prepareNonunits();
    std::vector<std::pair<int,int>> jobs;
    for (int g=1;g<n;++g) if (n%g==0 && (!only || g==only || (only == -1 && g>1)) && !(g>1 && n<1024 && distinctPrimes<=2))
        for (int z=std::min(hi,nonunitWitness?n-1:n-8);z>=std::max(g+1,lo);--z) jobs.emplace_back(g,z);
    std::atomic<std::size_t> task{0}; std::mutex lock;
    Counts sums{}; std::vector<std::thread> pool;
    for (int w=0;w<threads;++w) pool.emplace_back([&] {
        while (true) {
            auto i=task.fetch_add(1);
            if (i>=jobs.size()) break;
            Search s{m,jobs[i].first,jobs[i].second,{}, {}, {}};
            s.run(nonunitWitness);
            std::lock_guard<std::mutex> guard(lock);
            for (int j=0;j<12;++j) sums[j]+=s.counts[j];
            for (auto& a:s.leaves) { std::cout<<"FOUND "<<n; for (auto x:a) std::cout<<' '<<x; std::cout<<std::endl; }
        }
    });
    for (auto& t:pool) t.join();
    std::cout<<"complete "<<n<<' '<<only<<' '<<lo<<' '<<hi<<" shards "<<jobs.size()<<" leaves "<<sums[10]<<" full-balls "<<sums[0]<<" capacity "<<sums[1]<<" subgroups "<<sums[11]<<" nodes";
    for (int k=3;k<=8;++k) std::cout<<' '<<sums[k];
    for(int x:m.seed) std::cout<<" seed "<<x;
    std::cout<<std::endl;
}
