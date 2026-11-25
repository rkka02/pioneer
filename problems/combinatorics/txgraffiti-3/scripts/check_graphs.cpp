// Read simple regular graphs in short graph6 format (1..62 vertices).
// --exact computes both minima. --dual also checks the complementary degree.
#include "regular_graph.hpp"

static bool inspect(const Graph& g, const std::string& record, bool exact, bool complement) {
    int lower = g.matching_bound();
    if (!exact && g.independent_domination(g.all, lower)) return false;
    int i = exact ? (g.n + g.degree) / (g.degree + 1) : lower + 1;
    while (!g.independent_domination(g.all, i)) ++i;
    if (!exact && !g.maximal_matching(g.all, i - 1)) return false;
    int mu = lower;
    while (!g.maximal_matching(g.all, mu)) ++mu;
    if (complement) std::cout << "complement-of ";
    std::cout << record << " n=" << g.n << " r=" << g.degree
              << " i=" << i << " mu=" << mu << '\n';
    return i > mu;
}

int main(int argc, char** argv) {
    bool exact = argc == 2 && std::string(argv[1]) == "--exact";
    bool dual = argc == 2 && std::string(argv[1]) == "--dual";
    if (argc > 1 && !exact && !dual) return 2;
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    std::uint64_t tested = 0, violations = 0;
    for (std::string s; std::getline(std::cin, s);) {
        Graph g(s);
        if (!dual && !g.degree) throw std::runtime_error("positive regular degree required");
        if (g.degree) {
            ++tested;
            violations += inspect(g, s, exact, false);
        }
        const int other_degree = g.n - 1 - g.degree;
        if (dual && other_degree > 0 && other_degree != g.degree) {
            g.complement();
            ++tested;
            violations += inspect(g, s, exact, true);
        }
    }
    std::cerr << "tested=" << tested << " violations=" << violations << '\n';
}
