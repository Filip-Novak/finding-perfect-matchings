#ifndef BA_GRAPH_SAT_CNF_COLOURING_HPP
#define BA_GRAPH_SAT_CNF_COLOURING_HPP

#include "cnf.hpp"
#include "../invariants/degree.hpp"
#include "../operations/line_graph.hpp"
#include "../operations/simplification.hpp"

#include <cassert>
#include <map>
#include <vector>

namespace ba_graph
{

// for each of the vertices in precolouring that has colour from {0, 1, ..., k-1}
// it gets that colour
inline CNF cnf_vertex_colouring(const Graph &G, int k, VertexLabeling<int> precolouring)
{
    if (k == 0 && G.order() == 0) return cnf_satisfiable;
    if (k == 0 && G.order() > 0) return cnf_unsatisfiable;

    std::map<Number, std::vector<int>> vars;
    int nextVar = 0;
    for (auto &r : G) {
        std::vector<int> v(k);
        for (int i = 0; i < k; ++i)
            v[i] = nextVar++;
        vars[r.n()] = v;
    }

    std::vector<std::vector<Lit>> result;
    result.reserve(G.order() * (1 + k*k) + G.size() * k);
    for (auto &r : G) {
        int preC = precolouring[r.v()];
#ifdef BA_GRAPH_DEBUG
        if (preC != -1) {
            assert(preC < k);
            assert(preC >= 0);
        }
#endif

        std::vector<Lit> clause1;
        clause1.reserve(k);
        // at least one colour for the vertex
        for (int c = 0; c < k; ++c) {
            // if precoloured by c, this vertex gets only colour c
            if ((preC == -1) || (preC == c))
                clause1.push_back(Lit(vars[r.n()][c], false));
        }
        result.push_back(clause1);

        if (preC == -1) {
            // at most one colour for the vertex
            for (int c1 = 0; c1 < k; ++c1) {
                for (int c2 = c1 + 1; c2 < k; ++c2) {
                    result.push_back({
                            Lit(vars[r.n()][c1], true),
                            Lit(vars[r.n()][c2], true)
                    });
                }
            }
        }

        // no adjacent vertices have the same colour
        for (auto &i : r) {
            if (i.n2() <= r.n())
                continue;
            int preC2 = precolouring[i.v2()], preC1 = preC;
            for (int c = 0; c < k; ++c) {
                Lit lit1 = Lit(vars[r.n()][c], true);
                Lit lit2 = Lit(vars[i.n2()][c], true);
                if ((preC1 == -1) && (preC2 == -1)) {
                    result.push_back({lit1, lit2});
                } else if ((preC1 == -1) && (preC2 != -1)) {
                    if (c == preC2) result.push_back({lit1});
                } else if ((preC1 != -1) && (preC2 == -1)) {
                    if (c == preC1) result.push_back({lit2});
                } else {
                    if (preC1 == preC2)
                        return cnf_unsatisfiable;
                }
            }
        }
    }
    return std::pair(G.order() * k, result);
}

// if precolour = true, precolour two adjacent vertices by 0 and 1
// perhaps could be improved by finding a bigger clique
inline CNF cnf_vertex_colouring(const Graph &G, int k, bool precolour = false)
{
    VertexLabeling<int> precolouring(-1);
    if (!precolour)
        return cnf_vertex_colouring(G, k, precolouring);
    if (G.size() >= 1) {
        if (k == 0)
            return cnf_unsatisfiable;
        Edge e = G.find(RP::all(), IP::all()).second->e();
        precolouring.set(e.v1(), 0);
        if (k >= 2)
            precolouring.set(e.v2(), 1);
        else
            return cnf_unsatisfiable;
    }
    return cnf_vertex_colouring(G, k, precolouring);
}

// for each of the edges in precolouring that has colour from {0, 1, ..., k-1}
// it gets that colour
inline CNF cnf_edge_colouring(const Graph &G, int k, EdgeLabeling<int> precolouring)
{
    Factory f;
    auto [H, edgeToVertex] = line_graph_with_map(G, f);
    VertexLabeling<int> lgPrecolouring(-1);
    for (Edge e : G.list(RP::all(), IP::primary(), IT::e())) {
        lgPrecolouring.set(H[edgeToVertex[e]].v(), precolouring[e]);
    }
    return cnf_vertex_colouring(H, k, lgPrecolouring);
}

// if precolour = true, precolour the edges from a vertex of maximum degree by colour 0, 1, ...
inline CNF cnf_edge_colouring(const Graph &G, int k, bool precolour = false)
{
    Factory f;
    auto [H, edgeToVertex] = line_graph_with_map(G, f);
    VertexLabeling<int> precolouring(-1);
    if (!precolour)
        return cnf_vertex_colouring(H, k);

    int d = max_deg(G);
    if (k < d)
        return cnf_unsatisfiable;
    for (auto &r : G) {
        if (r.contains(r.n())) // there is a loop in G
            return cnf_unsatisfiable;
        if (r.degree() == d) {
            int c = 0;
            for (Edge e : r.list(IP::all(), IT::e()))
                precolouring.set(H[edgeToVertex[e]].v(), c++);
            break;
        }
    }
    return cnf_vertex_colouring(H, k, precolouring);
}

}  // namespace end

#endif
