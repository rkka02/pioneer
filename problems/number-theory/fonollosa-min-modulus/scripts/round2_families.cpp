// Exact witness search for the Round 2 construction families.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
using I=std::int64_t;
using V=std::vector<int>;
int mod(I x,int m){ int t=x%m; return t<0?t+m:t; }
int endpoint(int n){ return (1<<n)-(1<<(31-__builtin_clz(unsigned(n)))); }
int prime(int n){ for(int p=n;;++p){bool ok=p>=2;for(int i=2;i*i<=p;++i) if(p%i==0)ok=false;if(ok)return p;} }

struct Result { int size; std::uint64_t witness; int simple=0; V rival={}; };
// An alternative to a squarefree k-submultiset certifies a rival in the full set.
Result test(const V& a,int N) {
    const int n=a.size();
    if (std::set<int>(a.begin(),a.end()).size()!=a.size()) return {-1,0};
    std::vector<int> index(N,-1);
    for(int k=2;k<=std::min(6,n);++k) {
        auto subsets=[&](auto&& self,int pos,int need,int s,int mask)->void {
            if(!need){index[s]=mask;return;}
            for(int j=pos;j<=n-need;++j) self(self,j+1,need-1,mod(s+a[j],N),mask|(1<<j));
        };
        subsets(subsets,0,k,0,0);
        V chosen(k); int simple=0;
        std::uint64_t code=0;
        auto multisets=[&](auto&& self,int pos,int depth,int s,int mask)->bool {
            if(depth==k){
                if (index[s]<0 || index[s]==mask) return false;
                simple=index[s]; int lhs=0,rhs=0;
                for(int i=0;i<n;++i) if(index[s]&(1<<i)) lhs+=a[i];
                for(int i:chosen) { rhs+=a[i]; code=code*23+i+1; }
                if (__builtin_popcount(unsigned(index[s]))!=k || mod(lhs-rhs,N)) throw std::logic_error("certificate");
                code^=std::uint64_t(index[s])<<32;
                return true;
            }
            for(int j=pos;j<n;++j){chosen[depth]=j;if(self(self,j,depth+1,mod(s+a[j],N),mask|(1<<j)))return true;}
            return false;
        };
        if(multisets(multisets,0,0,0,0))return {k,code,simple,chosen};
        std::fill(index.begin(),index.end(),-1);
    }
    // Exact full DP. Counts all unordered multisets, saturated at two.
    int sum=mod(std::accumulate(a.begin(),a.end(),I{0}),N);
    std::vector<std::vector<unsigned char>> dp(n+1,std::vector<unsigned char>(N));
    dp[0][0]=1;
    for(int x:a) for(int k=1;k<=n;++k){
        auto& row=dp[k]; const auto& prev=dp[k-1];
        for(int y=x;y<N;++y)row[y]=std::min(2,int(row[y])+prev[y-x]);
        for(int y=0;y<x;++y)row[y]=std::min(2,int(row[y])+prev[y+N-x]);
    }
    return {dp[n][sum]==1?0:n,0};
}

struct Tally {int cases=0,duplicates=0,shortRivals=0,fullRivals=0,valid=0;std::uint64_t hash=0;};
int main(int argc,char** argv){
    bool certificates=argc==2 && std::string(argv[1])=="--certificates";
    std::mt19937_64 rng(2607083662ULL);
    std::map<std::string,Tally> total;
    for(int n=10;n<=20;++n){
        int f=endpoint(n);
        auto run=[&](const std::string& name,int N,const V& a){
            auto r=test(a,N);
            if(certificates){
                std::cout<<"case "<<name<<' '<<n<<' '<<N<<' '<<r.size<<' '<<r.simple;
                for(int x:a)std::cout<<' '<<x;for(int j:r.rival)std::cout<<' '<<j;
                std::cout<<'\n';
            }
            auto& v=total[name];++v.cases;v.hash+=r.witness;
            if(r.size<0)++v.duplicates;else if(!r.size){++v.valid;std::cout<<"FOUND "<<name<<' '<<n<<' '<<N;for(int x:a)std::cout<<' '<<x;std::cout<<std::endl;}
            else if(r.size<=6)++v.shortRivals;else ++v.fullRivals;
        };
        int p=prime(n), q=prime(n+1);V ruler{0};std::set<int> diffs;
        for(int x=1;int(ruler.size())<n;++x){
            bool ok=true;for(int y:ruler)if(diffs.count(x-y))ok=false;
            if(ok){for(int y:ruler)diffs.insert(x-y);ruler.push_back(x);}
        }
        for(int delta:{1,2,3,5,9,17}){
            int N=f-delta;V a(n);
            I x=1;
            for(int i=0;i<n;++i){a[i]=mod(x,N);x*=3;}run("base3",N,a);
            for(int s=0;s<12;++s){
                x=1;for(int i=0;i<n;++i){a[i]=mod(x,N);x*=2+((s<3)?int(i%3==s):int(rng()%3==0));}
                run("mixed-radix",N,a);
            }
            for(auto [u,v]:std::vector<std::pair<int,int>>{{29,15},{39,20},{49,25},{63,32},{79,40},{89,45}}){
                __int128 powU=1,powV=1;
                for(int i=0;i<n;++i){a[i]=mod(I((powU+powV/2)/powV),N);if(i+1<n){powU*=u;powV*=v;}}
                run("geometric",N,a);
            }
            for(int i=0;i<n;++i)a[i]=mod(ruler[i],N);
            run("Golomb",N,a);
            for(int s=0;s<4;++s){
                for(int i=0;i<n;++i){int j=i+s;a[i]=mod(2*p*j+mod(I(j)*j,p),N);}
                run("Sidon",N,a);p=prime(p+1);
            }
            q=prime(n+1);
            for(int s=0;s<6;++s){do{q=prime(q+1);}while(q>=N);
                int M=N-N%q;
                for(int i=0;i<n;++i)a[i]=mod(I(q)*(1LL<<(i%(n-3)))+(i<n-3?0:1+i-(n-3)),M);
                if(M>=(1<<(n-1)))run("subgroup",M,a);
            }
        }
        int base=1;while((base+1)*(base+1)<f)++base;
        for(int j=0;j<6;++j){
            int u=base-j,v=(f-1)/u;while(std::gcd(u,v)!=1)--v;
            const int N=u*v;
            int inv=1;while(inv*u%v!=1)++inv;
            for(int s=0;s<16;++s){V a(n);int c=1,e=1;
                for(int i=0;i<n;++i){int left,right;
                    if(s<4){left=i<(n+1)/2?c:0;right=i<(n+1)/2?0:e;}
                    else if(s<8){left=c;right=i*i+i*s+1;}
                    else {left=(i+s)*(i+s)%u;right=int(rng()%v);}
                    a[i]=mod(left+I(u)*mod(I(inv)*(right-left),v),N);
                    c=mod(I(c)*(2+s%3),u);e=mod(I(e)*(2+(s+1)%3),v);
                }
                run("CRT",N,a);
            }
        }
        std::cout<<"finished size "<<n<<std::endl;
    }
    for(auto& [name,v]:total)std::cout<<name<<' '<<v.cases<<' '<<v.duplicates<<' '<<v.shortRivals<<' '<<v.fullRivals<<' '<<v.valid<<' '<<v.hash<<'\n';
}
