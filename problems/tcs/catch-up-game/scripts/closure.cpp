// Greatest closed defender classes, on the even-total parity of each board.
// Bit j describes deficit 2*j + parity(sum of the remaining weights).
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Mask = std::uint32_t;
using Gaps = std::uint16_t;
struct Truth { Gaps win, loss; };
struct Roles { Gaps defend, oppose; };

static Gaps reverse(Gaps x) {
#if defined(__clang__)
    return __builtin_bitreverse16(x);
#else
    x = ((x & 0x5555u)<<1) | ((x>>1)&0x5555u);
    x = ((x & 0x3333u)<<2) | ((x>>2)&0x3333u);
    x = ((x & 0x0f0fu)<<4) | ((x>>4)&0x0f0fu);
    return (x>>8) | (x<<8);
#endif
}

struct Transition {
    Gaps positive;
    int shift, right;
    Transition(int x, int child_parity)
        : positive(static_cast<Gaps>(~1u | child_parity)), shift((x+child_parity)/2),
          right(15-(x-child_parity)/2) {}
    Gaps move(Gaps stay, Gaps pass) const {
        return static_cast<Gaps>(((stay & positive) << shift) | (reverse(pass) >> right));
    }
};

static int parity(Mask mask) { return __builtin_parity(mask & 0x55555555u); }
static int weight(Mask bit) { return 1 + __builtin_ctz(bit); }
static int largest(Mask mask) { return 32 - __builtin_clz(mask); }
static bool dense(Mask mask) {
    return !mask || 3*__builtin_popcount(mask) > 2*largest(mask)+1;
}
static bool bank(Mask mask) {
    if (!mask) return true;
    const int top = largest(mask);
    int covered = 0;
    for (Mask m = mask & ~(Mask{1} << (top-1)); m; m &= m-1) {
        const int x = weight(m);
        if (x > covered+1) return false;
        covered += x;
        if (covered >= top) return true;
    }
    return false;
}
static Gaps capped(int cap, int p) {
    return cap < p ? 0 : static_cast<Gaps>((1u << ((cap-p)/2+1))-1);
}
static std::vector<Truth> outcomes(int n) {
    std::vector<Truth> table(Mask{1}<<n);
    table[0] = {0, static_cast<Gaps>(~1u)};
    for (Mask mask=1; mask<table.size(); ++mask) {
        Truth best{0,UINT16_MAX};
        const int p=parity(mask);
        for (Mask m=mask; m; m&=m-1) {
            const Mask bit=m & -m;
            const int x=weight(bit);
            const Transition t(x,p^(x&1));
            const auto child=table[mask^bit];
            best.win |= t.move(child.win,child.loss);
            best.loss &= t.move(child.loss,child.win);
        }
        table[mask]=best;
    }
    return table;
}

enum class Domain { drawn, density, brown, both, all };
static bool member(Domain target, Mask mask, bool drawn) {
    switch (target) {
        case Domain::drawn: return drawn;
        case Domain::density: return dense(mask);
        case Domain::brown: return bank(mask);
        case Domain::both: return dense(mask) && bank(mask);
        case Domain::all: return true;
    }
    return false;
}

struct Counts {
    std::uint64_t tied=0, lead1=0, lead2=0, behind1=0, behind2=0;
    std::uint64_t eligible=0, gate_fails=0;
    Mask first_failure=0, largest_tied_mask=0;
    int largest_card=-1;
};

// Scan the ordinary minimax table without allocating role tables. Report
// each maximum separately so a new layer can be compared with earlier runs.
static void density_profiles(const std::vector<Truth> &truth, int n) {
    for (int top=1; top<=n; ++top) {
        std::array<std::array<std::uint64_t,3>,2> count{};
        std::array<Mask,2> witness{};
        int k=1;
        while (k*(k+1)/2<top) ++k;
        const Mask prefix=(Mask{1}<<k)-1;
        for (Mask mask=Mask{1}<<(top-1); mask<(Mask{1}<<top); ++mask) {
            if (parity(mask)) continue;
            const bool dense_board=3*__builtin_popcount(mask)>2*top+1;
            const bool prefix_bank=k<top && (mask & prefix)==prefix;
            if (!dense_board && !prefix_bank) continue;
            const Truth v=truth[mask];
            const int col=(v.win&1)?0:(v.loss&1)?2:1;
            for (int j=0; j<2; ++j) if (j?prefix_bank:dense_board) {
                ++count[j][col];
                if (!witness[j] && col!=1) witness[j]=mask;
            }
        }
        std::cout << top;
        for (int j=0; j<2; ++j) {
            for (auto total:count[j]) std::cout << '\t' << total;
            std::cout << '\t' << witness[j];
        }
        std::cout << std::endl;
    }
}

// In isolated mode a positive handoff uses the extra opponent state. Its next
// defender turn must finish at equality. Each allowed exact handoff restores mode 0.
template<bool Isolated, bool WinningExit>
static void solve(int n, int cap, int rank, Domain target, bool assume, bool dump, const std::vector<Truth> &truth) {
    constexpr int modes=Isolated ? 2 : 1;
    using Record=std::array<Roles,modes>;
    std::vector<Record> table(Mask{1}<<n);
    for (Roles &r : table[0]) r={1,UINT16_MAX};
    Counts c;
    c.tied=c.eligible=1;
    c.lead2=1; // An empty board with the opponent behind by two is already won.
    c.largest_card=0;
    if (dump) for (int d=0; d<=n; d+=2) std::cout << "state 0 " << d << ' ' << (d==0) << " 1\n";
    for (Mask mask=1; mask<table.size(); ++mask) {
        const int p=parity(mask);
        Record best;
        for (Roles &r:best) r={0,UINT16_MAX};
        for (Mask m=mask; m; m&=m-1) {
            const Mask bit=m & -m;
            const int x=weight(bit), cp=p^(x&1);
            const Transition step(x,cp);
            const Mask rest=mask^bit;
            const Record &child=table[rest];
            const Gaps zero=cp ? 0 : 1;
            const Gaps on_tie=child[0].oppose & zero;
            int local_cap=cap;
            if (rank) {
                Mask upper=rest;
                for (int j=1; j<rank && upper; ++j) upper&=upper-1;
                local_cap=upper ? std::min(n,weight(upper)+cap) : n;
            }
            const Gaps on_lead=child[modes-1].oppose & capped(local_cap,cp) & ~zero;
            best[0].defend |= step.move(child[0].defend,on_tie|on_lead);
            best[0].oppose &= step.move(child[0].oppose,child[0].defend);
            if constexpr (Isolated) {
                best[1].defend |= step.move(child[1].defend,on_tie);
                best[1].oppose &= step.move(child[1].oppose,child[1].defend);
            }
        }
        if constexpr (WinningExit) {
            for (Roles &r:best) {
                r.defend |= truth[mask].win;
                r.oppose |= truth[mask].loss;
            }
        }
        if (p==0) {
            const bool drawn=target!=Domain::drawn || ((truth[mask].win | truth[mask].loss)&1)==0;
            const bool in=member(target,mask,drawn), raw=best[0].oppose&1;
            if (in) {
                ++c.eligible;
                if (!raw) { ++c.gate_fails; if (!c.first_failure) c.first_failure=mask; }
            }
            for (Roles &r:best) {
                const bool closed=in && (assume || (r.oppose & 1));
                r.oppose=(r.oppose & ~1u) | closed;
            }
            if (in && raw) {
                ++c.tied;
                const int size=__builtin_popcount(mask);
                if (size>c.largest_card) { c.largest_card=size; c.largest_tied_mask=mask; }
            }
        }
        table[mask]=best;
        const Gaps hand=best[modes-1].oppose;
        if (p) {
            c.lead1+=hand&1; c.behind1+=best[0].defend&1;
        } else {
            c.lead2+=(hand>>1)&1; c.behind2+=(best[0].defend>>1)&1;
        }
        if (dump) {
            for (int d=p; d<=n; d+=2)
                std::cout << "state " << mask << ' ' << d << ' ' << ((best[0].defend>>(d/2))&1)
                          << ' ' << (((d ? hand : best[0].oppose)>>(d/2))&1) << '\n';
        }
        if ((mask & (mask+1))==0 && p==0) {
            const int k=largest(mask);
            const Mask suffix=mask & ~Mask{3};
            std::cout << "prefix " << k << " tied " << (best[0].oppose&1)
                      << " suffix_at_one_defender " << (table[suffix][0].defend&1)
                      << " suffix_at_one_opponent " << (table[suffix][modes-1].oppose&1)
                      << " opening_one " << (table[mask^1][0].oppose&1) << '\n';
        }
    }
    std::cout << "total " << n << " tied " << c.tied << " lead1 " << c.lead1 << " lead2 " << c.lead2
              << " behind1 " << c.behind1 << " behind2 " << c.behind2
              << " eligible " << c.eligible << " rejected " << c.gate_fails << " first " << c.first_failure
              << " maxcard " << c.largest_card << " example " << c.largest_tied_mask << std::endl;
}

int main(int argc,char** argv) {
    try {
        if (argc<3) throw std::runtime_error("usage: closure N K [--isolated] [--winning-exit] [--density|--brown|--both|--all-ties] [--assume] [--dump] [--pure] [--rank r] [--profiles]");
        const int n=std::stoi(argv[1]), k=std::stoi(argv[2]);
        if (n<2 || n>31 || k<0 || k>31) throw std::runtime_error("need N=2..31 and K=0..31");
        bool isolated=false, winning=false, assume=false, dump=false,pure=false,profiles=false;
        int rank=0;
        Domain target=Domain::drawn;
        for (int i=3;i<argc;++i) {
            const std::string arg=argv[i];
            if (arg=="--isolated") isolated=true;
            else if (arg=="--winning-exit") winning=true;
            else if (arg=="--assume") assume=true;
            else if (arg=="--dump") dump=true;
            else if (arg=="--pure") pure=true;
            else if (arg=="--profiles") profiles=true;
            else if (arg=="--rank" && i+1<argc) {
                rank=std::stoi(argv[++i]);
                if (rank<1 || rank>n) throw std::runtime_error("rank must be between 1 and N");
            }
            else if (arg=="--density") target=Domain::density;
            else if (arg=="--brown") target=Domain::brown;
            else if (arg=="--both") target=Domain::both;
            else if (arg=="--all-ties") target=Domain::all;
            else throw std::runtime_error("unknown argument "+arg);
        }
        if (pure) {
            // The least token refutes every nonempty board. Verify the obstruction
            // independently on each even mask without constructing minimax rows.
            std::uint64_t rejected=0;
            for (Mask m=1; m<(Mask{1}<<n); ++m) if (!parity(m)) {
                const Mask rest=m & (m-1);
                if (rest && weight(rest)<=weight(m)) throw std::logic_error("invalid minimum");
                ++rejected;
            }
            std::cout << "pure " << n << " core 1 rejected " << rejected << '\n';
            return 0;
        }
        const auto truth=(profiles || winning || target==Domain::drawn) ? outcomes(n) : std::vector<Truth>{};
        if (profiles) { density_profiles(truth,n); return 0; }
        if (isolated && winning) solve<true,true>(n,k,rank,target,assume,dump,truth);
        else if (isolated) solve<true,false>(n,k,rank,target,assume,dump,truth);
        else if (winning) solve<false,true>(n,k,rank,target,assume,dump,truth);
        else solve<false,false>(n,k,rank,target,assume,dump,truth);
    } catch(const std::exception &e) { std::cerr<<e.what()<<'\n'; return 1; }
}
