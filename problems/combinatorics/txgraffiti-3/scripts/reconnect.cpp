// Delete some planted matching edges and two unmatched vertices. Enumerate all
// ways to pair the dangling edge ends while keeping the remaining matching maximal.
#include "regular_graph.hpp"
#include <vector>

struct Reconnect {
    Graph g;
    int pairs, remove_pairs;
    std::uint64_t trials = 0, violations = 0;

    bool connected(Mask s) const {
        Mask seen = 0, todo = bit(first(s));
        while (todo) {
            int v = first(todo);
            seen |= bit(v);
            todo = (todo | (g.adj[v] & s)) & ~seen;
        }
        return seen == s;
    }

    void print_graph(Mask s) const {
        std::cout << char(size(s) + 63);
        int acc = 0, used = 0;
        for (Mask vv = s; vv; vv &= vv - 1) {
            int v = first(vv);
            for (Mask uu = s & (bit(v) - 1); uu; uu &= uu - 1) {
                acc = 2 * acc + bool(g.adj[v] & bit(first(uu)));
                if (++used == 6) {
                    std::cout << char(acc + 63);
                    acc = used = 0;
                }
            }
        }
        if (used) std::cout << char((acc << (6 - used)) + 63);
        std::cout << std::endl;
    }

    void complete(Mask s, const std::vector<int>& ports, Mask unpaired) {
        if (!unpaired) {
            ++trials;
            if (!g.independent_domination(s, pairs - remove_pairs) && connected(s)) {
                ++violations;
                print_graph(s);
            }
            return;
        }
        int p = first(unpaired), a = ports[p];
        unpaired ^= bit(p);
        int previous = -1;
        for (Mask q = unpaired; q; q &= q - 1) {
            int j = first(q), b = ports[j];
            if (b == previous) continue;
            previous = b;
            if (a == b || (a >= 2*pairs && b >= 2*pairs) || (g.adj[a] & bit(b))) continue;
            g.adj[a] ^= bit(b); g.closed[a] ^= bit(b);
            g.adj[b] ^= bit(a); g.closed[b] ^= bit(a);
            complete(s, ports, unpaired ^ bit(j));
            g.adj[a] ^= bit(b); g.closed[a] ^= bit(b);
            g.adj[b] ^= bit(a); g.closed[b] ^= bit(a);
        }
    }

    void delete_vertices(Mask removed) {
        Mask s = g.all ^ removed;
        std::vector<int> ports;
        for (Mask p = removed; p; p &= p - 1)
            for (Mask q = g.adj[first(p)] & s; q; q &= q - 1)
                ports.push_back(first(q));
        // Unmatched ports can only be paired with matched ports.
        std::sort(ports.rbegin(), ports.rend());
        auto count = std::count_if(ports.begin(), ports.end(), [this](int v) { return v >= 2*pairs; });
        if (2 * count <= static_cast<int>(ports.size()))
            complete(s, ports, bit(ports.size()) - 1);
    }

    void choose_pairs(int next, int left, Mask removed) {
        if (left) {
            for (int i = next; i <= pairs - left; ++i)
                choose_pairs(i+1, left-1, removed | bit(2*i) | bit(2*i+1));
            return;
        }
        for (int a = 2*pairs; a < g.n; ++a)
            for (int b = a+1; b < g.n; ++b)
                delete_vertices(removed | bit(a) | bit(b));
    }
};

int main(int argc, char** argv) {
    if (argc != 3) return 2;
    for (std::string record; std::getline(std::cin, record);) {
        Reconnect search{Graph(record), std::stoi(argv[1]), std::stoi(argv[2])};
        int k = search.pairs;
        if (search.g.degree != 3 || k < 1 || 2*k >= search.g.n || search.remove_pairs < 1
                || search.remove_pairs > 2 || search.remove_pairs >= k) return 2;
        for (int i = 0; i < k; ++i)
            if (!(search.g.adj[2*i] & bit(2*i+1))) return 2;
        Mask unmatched = search.g.all & ~(bit(2*k) - 1);
        for (Mask p = unmatched; p; p &= p - 1)
            if (search.g.adj[first(p)] & unmatched) return 2;
        search.choose_pairs(0, search.remove_pairs, 0);
        std::cerr << "reconnections=" << search.trials << " connected_violations=" << search.violations << '\n';
    }
}
