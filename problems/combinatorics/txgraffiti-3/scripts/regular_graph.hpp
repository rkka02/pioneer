#pragma once

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>

using Mask = std::uint64_t;

static Mask bit(int v) { return Mask{1} << v; }
static int first(Mask m) { return std::countr_zero(m); }
static int size(Mask m) { return std::popcount(m); }

struct Graph {
    int n, degree;
    Mask all;
    std::array<Mask, 62> adj{}, closed{};

    explicit Graph(const std::string& line) {
        n = line.empty() ? 0 : line[0] - 63;
        if (n < 1 || n > 62 || line.size() != 1u + (n * (n - 1) / 2 + 5) / 6)
            throw std::runtime_error("invalid short graph6 record");
        if (!std::all_of(line.begin(), line.end(), [](char c) { return c >= 63 && c <= 126; }))
            throw std::runtime_error("invalid graph6 character");
        all = bit(n) - 1;
        int k = 0;
        for (int v = 0; v < n; ++v) {
            for (int u = 0; u < v; ++u, ++k) {
                if ((line[1 + k / 6] - 63) >> (5 - k % 6) & 1) {
                    adj[u] |= bit(v);
                    adj[v] |= bit(u);
                }
            }
        }
        degree = size(adj[0]);
        for (int v = 0; v < n; ++v) {
            if (size(adj[v]) != degree)
                throw std::runtime_error("regular graph required");
            closed[v] = adj[v] | bit(v);
        }
    }

    void complement() {
        degree = n - 1 - degree;
        for (int v = 0; v < n; ++v) {
            adj[v] = all ^ closed[v];
            closed[v] = adj[v] | bit(v);
        }
    }

    // The remaining vertices are exactly the ones undominated by the independent
    // set already selected. Every extension must hit the pivot's closed neighborhood.
    bool independent_domination(Mask remaining, int budget) const {
        if (!remaining) return true;
        if (size(remaining) > budget * (degree + 1)) return false;
        Mask choices = remaining;
        for (Mask p = remaining; p; p &= p - 1) {
            Mask candidates = closed[first(p)] & remaining;
            if (size(candidates) < size(choices)) choices = candidates;
            if (std::has_single_bit(choices)) break;
        }
        for (; choices; choices &= choices - 1)
            if (independent_domination(remaining & ~closed[first(choices)], budget - 1))
                return true;
        return false;
    }

    // In the remaining induced graph, some matching edge must meet a fixed edge.
    // Removing both endpoints of the chosen edge leaves the same subproblem.
    bool maximal_matching(Mask remaining, int budget) const {
        int degree_sum = 0, u = -1, v = -1, best = 2 * degree + 1;
        for (Mask p = remaining; p; p &= p - 1) {
            int a = first(p);
            Mask neighbors = adj[a] & remaining;
            degree_sum += size(neighbors);
            if (!neighbors) continue;
            int b = first(neighbors);
            int cost = size(neighbors) + size(adj[b] & remaining);
            if (cost < best) { best = cost; u = a; v = b; }
        }
        if (u < 0) return true;
        if (degree_sum > 2 * budget * (2 * degree - 1)) return false;
        for (int a : {u, v}) {
            Mask choices = adj[a] & remaining;
            if (a == v) choices &= ~bit(u); // uv was tried in the first iteration
            for (; choices; choices &= choices - 1)
                if (maximal_matching(remaining & ~bit(a) & ~bit(first(choices)), budget - 1))
                    return true;
        }
        return false;
    }

    int matching_bound() const {
        int cover = 2 * degree - 1;
        return (n * degree / 2 + cover - 1) / cover;
    }
};
