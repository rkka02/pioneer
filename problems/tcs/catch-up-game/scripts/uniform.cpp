// A successful fixed-player strategy works after every common translation t >= 0.
// A flat deficit is d, a rising deficit is d+t. At an ambiguous comparison
// the branch fails certification for either designated role.
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include "subset_tiles.hpp"

using Mask = std::uint64_t;
using Bits = std::uint32_t;
struct Row { Bits acts, waits; };

class Uniform {
    int low, count;
    Mask odd = 0;
    std::vector<Row> rows, lower_dump;
    std::array<Row,32> lower_queries{};
    Mask top_bit;

public:
    Uniform(int first, int size, bool flat_max, unsigned workers, bool dump)
        : low(first), count(size), rows(Mask{1} << (size-1)), top_bit(rows.size()) {
        for (int i=0; i<count; ++i) if ((low+i)&1) odd |= Mask{1}<<i;
        // Acts uses reversed bit order and waits uses forward bit order.
        rows[0] = {Bits{1}<<31, ~Bits{0}};
        // The top-absent row at the current index is consumed by taking the
        // top token. Other moves read strict submasks in the current sweep.
        for (bool topped:{false,true}) {
            catchup::subset_tiles(count-1,workers,[&](unsigned,Mask start,Mask end) {
                for (Mask m=start;m<end;++m) {
                    const Mask s=topped ? m|top_bit : m;
                    if (!s) continue;
                    const unsigned p=__builtin_parityll(s&odd);
                    const bool rising=__builtin_parityll(s);
                    Row best{0,~Bits{0}};
                    for (Mask moves=s; moves; moves &= moves-1) {
                        const Mask bit=moves & -moves;
                        const unsigned x=low+__builtin_ctzll(bit), c=p^(x&1);
                        const unsigned shift=(x+c)/2, cross=31-(x-c)/2;
                        const Row child=rows[bit==top_bit ? m : m^bit];
                        Bits acts=child.waits << cross, waits=child.acts >> cross;
                        if (rising) {
                            const Bits same_acts=c ? child.acts : child.acts & ~(Bits{1}<<31);
                            const Bits same_waits=c ? child.waits : child.waits & ~Bits{1};
                            acts |= Mask(same_acts) >> shift;
                            waits |= Mask(same_waits) << shift;
                        }
                        if (rising || !flat_max || bit>(s^bit)) best.acts |= acts;
                        best.waits &= waits;
                    }
                    rows[m]=best;
                }
            });
            if (!topped) {
                if (dump) lower_dump=rows;
                const Mask all=top_bit-1;
                lower_queries[count-1]=rows[all];
                for (int i=0;i<count-1;++i) lower_queries[i]=rows[all ^ (Mask{1}<<i)];
            }
        }
    }
    Mask full() const { return 2*top_bit-1; }
    std::pair<bool,bool> bounds(Mask s, int d) const {
        if (d<0 || d>63 || ((d&1)!=__builtin_parityll(s&odd))) throw std::runtime_error("gap parity or range");
        Row r;
        if (s & top_bit) r=rows[s^top_bit];
        else if (!lower_dump.empty()) r=lower_dump[s];
        else {
            const Mask missing=(top_bit-1)^s;
            if (missing & (missing-1)) throw std::logic_error("uncaptured lower row");
            r=lower_queries[missing ? __builtin_ctzll(missing) : count-1];
        }
        return {bool((r.acts>>(31-d/2))&1),bool((r.waits>>(d/2))&1)};
    }
    void report(int n, bool dump, bool holes) const {
        const int mid=low+n-1;
        const auto root=bounds(full(),mid);
        std::string picks;
        for (int i=0;i<count;++i) {
            const int x=low+i;
            const auto [mover, other]=bounds(full()^(Mask{1}<<i),std::abs(x-mid));
            const bool first=x<mid ? mover : other, second=x<mid ? other : mover;
            // B means both holds. 1 or 2 certifies only the indicated role.
            picks += first ? (second?'B':'1') : (second?'2':'?');
        }
        std::cout<<n<<' '<<low<<' '<<root.first<<' '<<root.second<<' '<<picks<<'\n';
        if (holes) {
            int lower=0, lower_total=0, upper=0, max_works=0;
            for (int i=0;i<count;++i) {
                const Mask after=full()^(Mask{1}<<i);
                const int x=low+i, small=std::abs(x-mid);
                for (int j=0;j<count;++j) if (i!=j) {
                    const int y=low+j;
                    if (y<small) throw std::runtime_error("two-pick report needs a passing flat reply");
                    const auto [acts,waits]=bounds(after^(Mask{1}<<j),y-small);
                    if (x<mid) {
                        ++lower_total;
                        lower+=acts;
                    } else {
                        upper+=waits;
                        if (j==63-__builtin_clzll(after)) max_works+=waits;
                    }
                }
            }
            std::cout<<"two-pick "<<n<<' '<<lower<<'/'<<lower_total<<' '<<upper<<' '<<max_works<<'\n';
        }
        if (dump) {
            for (Mask s=0;s<=full();++s)
                for (int d=__builtin_parityll(s&odd); d<=low+count-1; d+=2) {
                    const auto [a,b]=bounds(s,d);
                    std::cout<<s<<' '<<d<<' '<<a<<' '<<b<<'\n';
                }
        }
    }
};

int main(int argc,char** argv) {
    try {
        if (argc<2) throw std::runtime_error("uniform n [base] [--dump] [--holes] [--flat-max] [--workers k]");
        const int n=std::stoi(argv[1]);
        int a=2*n+1;
        bool dump=false, holes=false, flat_max=false;
        int workers=1;
        for (int i=2;i<argc;++i) {
            const std::string arg=argv[i];
            if (arg=="--workers" && i+1<argc) workers=std::stoi(argv[++i]);
            else if (arg=="--dump") dump=true;
            else if (arg=="--holes") holes=true;
            else if (arg=="--flat-max") flat_max=true;
            else if (i==2) a=std::stoi(arg);
            else throw std::runtime_error("unknown option");
        }
        if (n<1 || n>16 || a<1 || a+2*n-2>63) throw std::runtime_error("need 1..16 pairs and maximum <=63");
        if (workers<1 || workers>32) throw std::runtime_error("workers must be 1..32");
        Uniform(a,2*n-1,flat_max,workers,dump).report(n,dump,holes);
    } catch (const std::exception& error) {
        std::cerr<<error.what()<<'\n'; return 1;
    }
}
