// Check whether an opener can reach half the total against every reply.
// Below the chosen suffix, the defender may take one of the k smallest live
// tokens. The opponent is unrestricted. A successful restricted search is a proof.
#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <iostream>
#include <mutex>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>
#include "paircuts.hpp"

using Mask = std::uint64_t;
using Gaps = std::uint32_t;
struct MemoRow { std::array<Gaps, 2> known{}, hold{}; };
struct GoalRow { Gaps defender, opponent; };

class Defense {
    int n, free_count, choices, half, handoff_rank;
    bool endpoints;
    bool use_pairs;
    int adaptive_free;
    Mask low_mask;
    std::vector<MemoRow> suffix;
    std::vector<GoalRow> complete;
    std::vector<Mask> cache;

    int lead_limit(Mask rest, int offset) const {
        for (int i=1; i<handoff_rank && rest; ++i) rest &= rest-1;
        return rest ? offset+1+__builtin_ctzll(rest) : n;
    }

    void build_suffix() {
        // Fixed defender, fixed half-total goal. Lower deficits run from right to left
        // in the defender word (bit 31 is the smallest) and left to right in the
        // opponent word (bit 0 is the smallest). Passing then needs no bit reversal.
        const int base = n-free_count;
        Mask odd_tokens = 0;
        for (int i = 0; i < free_count; ++i)
            if ((base+i+1) % 2) odd_tokens |= Mask{1} << i;
        complete.resize(Mask{1} << free_count);
        std::vector<Gaps> allowed;
        if (handoff_rank) {
            allowed.resize(complete.size());
            for (Mask rest=0; rest<complete.size(); ++rest) {
                const int p=__builtin_parityll(rest & odd_tokens);
                const int count=(lead_limit(rest,base)-p)/2+1;
                allowed[rest]=(Mask{1}<<count)-1;
            }
        }
        complete[0] = {Gaps{1} << 31, ~Gaps{0}};
        for (Mask board = 1; board < complete.size(); ++board) {
            const unsigned parity = __builtin_parityll(board & odd_tokens);
            GoalRow best{0, ~Gaps{0}};
            for (Mask moves = board; moves; moves &= moves-1) {
                const Mask bit = moves & -moves;
                const unsigned x = base + __builtin_ctzll(bit) + 1;
                const unsigned c = parity ^ (x & 1), shift = (x+c)/2, cross = 31-(x-c)/2;
                const GoalRow &child = complete[board ^ bit];
                const Gaps same_defender = c ? child.defender : child.defender & ~(Gaps{1} << 31);
                const Gaps same_opponent = c ? child.opponent : child.opponent & ~Gaps{1};
                const Gaps permitted=handoff_rank ? child.opponent & allowed[board^bit] : child.opponent;
                best.defender |= (same_defender >> shift) | (permitted << cross);
                best.opponent &= (same_opponent << shift) | (child.defender >> cross);
            }
            complete[board] = best;
        }
    }

    bool play(Mask board, int mine, int theirs, bool my_turn) {
        const int gap = my_turn ? theirs - mine : mine - theirs;
        if (handoff_rank) {
            const int sum=2*half-mine-theirs;
            if (sum<=gap) return !my_turn || sum==gap;
        } else {
            if (mine >= half || theirs == half) return true;
            if (theirs > half) return false;
        }
        // Board nonempty here, since both scores are strictly below half.
        const bool free = (board & low_mask) == 0;
        if (free && !complete.empty()) {
            const GoalRow &row = complete[board >> (n-free_count)];
            const unsigned k = gap/2;
            return my_turn ? (row.defender >> (31-k)) & 1 : (row.opponent >> k) & 1;
        }
        const int largest = 64-__builtin_clzll(board);
        if (!handoff_rank && !my_turn && theirs+largest > half) return false;
        if (!handoff_rank && my_turn && (free || choices >= n || endpoints) && mine+largest >= half) return true;
        // For a fixed board, gap and the sum already taken have the same parity.
        const std::uint32_t bit_gap = std::uint32_t{1} << (gap / 2);
        const Mask key = ((board * (half + 1) + mine) << 1) | my_turn;
        const Mask mixed = (key ^ (key >> 23)) * UINT64_C(0x9e3779b97f4a7c15);
        Mask &slot = cache[(mixed ^ (mixed >> 31)) & (cache.size() - 1)];
        if (free) {
            const MemoRow &row = suffix[board >> (n - free_count)];
            if (row.known[my_turn] & bit_gap) return (row.hold[my_turn] & bit_gap) != 0;
        } else {
            const Mask saved = __atomic_load_n(&slot,__ATOMIC_RELAXED);
            if ((saved >> 1) == key) return saved & 1;
        }

        bool holds = !my_turn; // existential defender, universal opponent
        Mask options = board;
        if (use_pairs && gap > 0) {
            const int count = __builtin_popcountll(board), low = 1 + __builtin_ctzll(board);
            const bool critical=count==2*gap && largest-low+1==count;
            if (critical && gap<=8 && low+1>=count) return true; // Either player holds.
            if (critical && low >= count+1) {
                if (!my_turn) return true;
                options = Mask{1} << (largest-1);
            } else {
                const int bound = catchup::pair_bound(board,1,gap);
                if (bound == 1 || (bound == 0 && !my_turn)) return !my_turn;
            }
        }
        if (my_turn && adaptive_free>=0 && __builtin_popcountll(board)>adaptive_free) {
            // All options here are legal: a two-token exact catch spends its
            // smaller positive token first, and then hands off at equality.
            for (int u=1; 2*u<gap; ++u) {
                const int v=gap-u;
                const Mask pair=(Mask{1}<<(u-1)) | (Mask{1}<<(v-1));
                if ((board & pair)!=pair) continue;
                const Mask rest=board^pair;
                if (rest && 3*__builtin_popcountll(rest)>2*(64-__builtin_clzll(rest))+1 &&
                        play(rest,theirs,theirs,false)) return true;
            }
            const Mask below=board & ((Mask{1} << std::max(0,gap-1))-1);
            const Mask above=board ^ below;
            Mask allowed=(board & -board) | (Mask{1}<<(largest-1));
            if (below) allowed |= Mask{1}<<(63-__builtin_clzll(below));
            if (above) allowed |= above & -above;
            options &= allowed;
        }
        if (my_turn && !free && choices < n) {
            Mask above_low = board, below_high = board;
            for (int i = 0; i < choices && above_low; ++i) {
                above_low &= above_low - 1;
                if (endpoints) below_high ^= Mask{1} << (63 - __builtin_clzll(below_high));
            }
            options &= ~(above_low & below_high);
        }
        for (Mask moves = options; moves; moves &= moves - 1) {
            const Mask bit = moves & -moves;
            const int x = __builtin_ctzll(bit) + 1;
            if (handoff_rank && my_turn && x>=gap && x-gap>lead_limit(board^bit,0)) continue;
            if (my_turn)
                holds = play(board ^ bit, mine + x, theirs, mine + x < theirs);
            else
                holds = play(board ^ bit, mine, theirs + x, theirs + x >= mine);
            if (holds == my_turn) break;
        }
        if (free) {
            MemoRow &row = suffix[board >> (n - free_count)];
            row.known[my_turn] |= bit_gap;
            if (holds) row.hold[my_turn] |= bit_gap;
        } else {
            __atomic_store_n(&slot,(key << 1) | holds,__ATOMIC_RELAXED);
        }
        return holds;
    }

public:
    Defense(int size, int suffix_size, int k, bool ends, bool packed, int rank, bool paired, int adaptive)
        : n(size), free_count(suffix_size), choices(k), half(n * (n + 1) / 4), handoff_rank(rank),
          endpoints(ends), use_pairs(paired), adaptive_free(adaptive), low_mask((Mask{1} << (n - free_count)) - 1), suffix(packed ? 0 : Mask{1} << free_count),
          cache(Mask{1} << (n >= 39 ? 25 : 23)) {
        if (packed) build_suffix();
    }
    bool second_holds(int a, int b) {
        const Mask remaining = ((Mask{1} << n)-1) ^ (Mask{1} << (a-1)) ^ (Mask{1} << (b-1));
        if (handoff_rank && b>=a && b-a>lead_limit(remaining,0)) return false;
        return play(remaining, b, a, b < a);
    }

    bool opening(int x) {
        if (handoff_rank && x > lead_limit(((Mask{1}<<n)-1) ^ (Mask{1}<<(x-1)),0)) return false;
        return play(((Mask{1} << n) - 1) ^ (Mask{1} << (x - 1)), x, 0, false);
    }
    bool tied_defense() { return play((Mask{1}<<n)-1,0,0,false); }
    bool defend_opening(int x) {
        return play(((Mask{1}<<n)-1) ^ (Mask{1}<<(x-1)),0,x,true);
    }
    void two_offsets() {
        if (n<4 || handoff_rank || choices<n) throw std::runtime_error("offsets need N>=4 and unrestricted opposing moves");
        const Mask full=(Mask{1}<<n)-1;
        const bool first=play(full^7,2,4,true), second=play(full^7,4,2,false);
        std::cout<<n<<" boundary "<<first<<' '<<second<<std::endl;
        for (int a:{2,3}) {
            std::cout<<n<<" holes "<<a;
            for (int x=a+1;x<=n;++x) {
                const Mask board=full ^ ((Mask{1}<<(a-1))-1) ^ (Mask{3}<<(x-2));
                const int tied=(a*(a-1)/2+2*x-1)/2;
                if (!play(board,tied,tied,false)) std::cout<<' '<<x;
            }
            std::cout<<std::endl;
        }
    }
    // Certify P1 separately after each possible second pick. The immutable
    // packed endgame and atomic full-key cache are shared among all workers.
    void split_openings(const std::vector<int>& openings, int workers) {
        if (complete.empty() || handoff_rank || choices<n || workers<1 || openings.empty())
            throw std::runtime_error("split openings need packed unrestricted play and at least one worker");
        std::vector<std::pair<int,int>> jobs;
        for (int b=1;b<=n;++b) for (int a:openings) {
            if (a<1 || a>n) throw std::runtime_error("opening outside board");
            if (a!=b) jobs.emplace_back(a,b);
        }
        std::atomic<std::size_t> next{0};
        std::mutex output;
        std::vector<std::thread> pool;
        for (int i=0;i<workers;++i) pool.emplace_back([&] {
            for (auto j=next.fetch_add(1);j<jobs.size();j=next.fetch_add(1)) {
                const auto [a,b]=jobs[j];
                const Mask rest=((Mask{1}<<n)-1) ^ (Mask{1}<<(a-1)) ^ (Mask{1}<<(b-1));
                const bool held=play(rest,a,b,b>=a);
                std::lock_guard<std::mutex> lock(output);
                std::cout<<n<<'\t'<<a<<'\t'<<b<<"\tP1\t"<<held<<std::endl;
            }
        });
        for (auto& worker:pool) worker.join();
    }
    void ray_positions(int low, int high) {
        if (handoff_rank || choices<n || low<2 || high>n || low>high)
            throw std::runtime_error("ray positions require unrestricted play and valid endpoints");
        for (int a=high; a>=low; --a) {
            const int taken=(a-1)*a/2, d=a/2;
            const int trailing=(taken-d)/2, leading=(taken+d)/2;
            const Mask board=((Mask{1}<<n)-1) ^ ((Mask{1}<<(a-1))-1);
            const bool mover=play(board,trailing,leading,true);
            const bool opponent=play(board,leading,trailing,false);
            if (!mover && !opponent) throw std::logic_error("inconsistent minimax bounds");
            std::cout << n << '\t' << a << '\t' << d << '\t' << (mover ? (opponent?'D':'W') : 'L')
                      << std::endl;
        }
    }
};

int main(int argc, char **argv) {
    try {
        if (argc < 5) throw std::runtime_error("usage: defense N free_top_count choices [--ends] [--packed] [--pair-cuts] [--rank r] [--tied|--defend|--split workers] opening ... (or --reply a b, --ray-positions lo hi)");
        int n = std::stoi(argv[1]), free_count = std::stoi(argv[2]), k = std::stoi(argv[3]);
        // At N=52 the board, score and two Boolean flags still fit a 64-bit key.
        if (n < 1 || n > 52 || (n * (n + 1) / 2) % 2 || free_count < 0 ||
            free_count > std::min(n, 30) || k < 1)
            throw std::runtime_error("need even total, N=1..52, suffix size 0..min(N,30), choices >=1");
        bool ends = false, packed = false, paired = false, reply = false, tied=false, defend=false, offsets=false;
        int rank=0, ray_lo=0, ray_hi=0, workers=0;
        int adaptive=-1;
        int first = 4;
        while (first < argc) {
            const std::string option = argv[first];
            if (option == "--ends") ends = true;
            else if (option == "--packed") packed = true;
            else if (option == "--pair-cuts") paired = true;
            else if (option == "--offsets") offsets=true;
            else if (option == "--adaptive" && first+1<argc) {
                adaptive=std::stoi(argv[++first]);
                if (adaptive<0 || adaptive>n) throw std::runtime_error("invalid unrestricted endgame size");
            }
            else if (option == "--split" && first+1<argc) {
                workers=std::stoi(argv[++first]);
                if (workers<1) throw std::runtime_error("need at least one worker");
            }
            else if (option == "--reply") reply = true;
            else if (option == "--tied") tied=true;
            else if (option == "--defend") defend=true;
            else if (option=="--ray-positions" && first+2<argc) {
                ray_lo=std::stoi(argv[++first]); ray_hi=std::stoi(argv[++first]);
            }
            else if (option == "--rank" && first+1<argc) {
                rank=std::stoi(argv[++first]);
                if (rank<1 || rank>n) throw std::runtime_error("rank must be between 1 and N");
            }
            else break;
            ++first;
        }
        if (first == argc && !tied && !ray_lo && !offsets) throw std::runtime_error("supply an opening");
        if (paired && (rank || k < n)) throw std::runtime_error("pair cuts require unrestricted defender moves");
        if (adaptive>=0 && (rank || free_count || k<n || workers))
            throw std::runtime_error("adaptive endpoints need zero suffix size, all choices and no rank limit");
        Defense verifier(n, free_count, k, ends, packed, rank, paired, adaptive);
        if (offsets) verifier.two_offsets();
        if (workers) {
            std::vector<int> openings;
            for (int i=first;i<argc;++i) openings.push_back(std::stoi(argv[i]));
            verifier.split_openings(openings,workers);
            return 0;
        }
        if (ray_lo) verifier.ray_positions(ray_lo,ray_hi);
        if (tied) std::cout << n << "\tP2 tied\t" << (verifier.tied_defense()?"holds":"fails") << std::endl;
        if (reply) {
            if (argc-first != 2) throw std::runtime_error("a conditional reply needs two distinct picks");
            const int a = std::stoi(argv[first]), b = std::stoi(argv[first+1]);
            if (a < 1 || a > n || b < 1 || b > n || a == b) throw std::runtime_error("invalid pair");
            std::cout << n << '\t' << a << '\t' << b << '\t'
                      << (verifier.second_holds(a,b) ? "P2 holds" : "P2 fails") << std::endl;
            return 0;
        }
        for (int i = first; i < argc; ++i) {
            const int x = std::stoi(argv[i]);
            if (x < 1 || x > n) throw std::runtime_error("opening outside board");
            const bool held=defend ? verifier.defend_opening(x) : verifier.opening(x);
            std::cout << n << '\t' << free_count << '\t' << k << '\t' << x << '\t'
                      << (defend?"P2 ":"") << (held ? "holds" : "fails") << std::endl;
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
