#ifndef BA_GRAPH_INVARIANTS_COLOURING_HPP
#define BA_GRAPH_INVARIANTS_COLOURING_HPP

#include "degree.hpp"
#include "invariants/girth.hpp"
#include "../operations/simplification.hpp"
#include "../operations/line_graph.hpp"
#include "../operations/basic.hpp"

#include <iostream>
#include <set>
#include <unordered_set>

namespace ba_graph
{

namespace internal
{

template <typename T = void>
class ColouringEnumerator
{
  public:
    const Graph *G;
    int k; // number of colours
    bool (*callback)(VertexLabeling<int>, T *param);
    T *callbackParam;
    int maxColourings = -1;

    int precolouredCount;
    std::vector<Number> ordering;
    std::vector<bool> surrounded;
    std::vector<int> colouring;
    int foundColouringsCount;
    bool doContinue;

    const int noColour = -1;

    ColouringEnumerator() {}

    // returns true iff precolouring is consistent
    bool computeOrdering(VertexLabeling<int> precolouring)
    {
        bool consistent = true;
        ordering.clear();
        ordering.reserve(G->order());
        surrounded.clear();
        surrounded.resize(max_number(*G).to_int() + 1);

        std::map<Number, int> nColouredNeighbours;
        for (auto &r : *G) {
            nColouredNeighbours[r.n()] = 0;
            surrounded[r.n().to_int()] = false;
        }

        std::set<Number> unused;
        for (auto &r : *G) {
            if (precolouring[r.v()] == -1) {
                unused.insert(r.n());
            } else {
#ifdef BA_GRAPH_DEBUG
                assert(precolouring[r.v()] < k);
                assert(precolouring[r.v()] >= 0);
#endif
                colouring[r.n().to_int()] = precolouring[r.v()];
                ordering.push_back(r.n());
                for (auto u : (*G)[r.n()].neighbours()) {
                    if (precolouring[(*G)[u].v()] == precolouring[r.v()])
                        consistent = false;
                    ++nColouredNeighbours[u];
                }
            }
        }
        precolouredCount = G->order() - unused.size();

        // next vertex is one that has maximum neighbours among those already coloured
        while (unused.size() > 0) {
            Number v;
            int max = -1;
            for (auto x : unused) {
                if (nColouredNeighbours[x] > max) {
                    v = x;
                    max = nColouredNeighbours[x];
                }
            }
            if ((*G)[v].degree() == max) // all neighbours of v are coloured
                surrounded[v.to_int()] = true;
            ordering.push_back(v);
            unused.erase(v);
            for (auto u : (*G)[v].neighbours())
                ++nColouredNeighbours[u];
        }
        return consistent;
    }

    bool colour(int next)
    {
        if (!doContinue)
            return false;

        if (next == G->order()) {
            ++foundColouringsCount;
            if (callback != NULL) {
                VertexLabeling<int> outputColouring(noColour);
                for (auto &r : *G)
                    outputColouring.set(r.v(), colouring[r.n().to_int()]);
                doContinue = callback(outputColouring, callbackParam);
            }
            return true;
        }

        Number v = ordering[next];
        bool found = false;
        if ((maxColourings == 1) && surrounded[v.to_int()]) {
            // we are only interested in the existence of a colouring
            std::unordered_set<int> s;
            for (auto &inc : (*G)[v])
                s.insert(colouring[inc.n2().to_int()]);
            return ((int)s.size() < k) ? colour(next + 1) : false;
        } else {
            for (int c = 0; c < k; c++) {
                bool used = false;
                for (auto &inc : (*G)[v]) {
                    if (colouring[inc.n2().to_int()] == c) {
                        used = true;
                        break;
                    }
                }
                if (!used) {
                    colouring[v.to_int()] = c;
                    if ((maxColourings == -1) || (foundColouringsCount < maxColourings)) {
                        bool r = colour(next + 1);
                        found = found || r;
                    }
                }
            }
        }
        colouring[v.to_int()] = noColour;
        return found;
    }

    // returns true iff at least one colouring was found
    bool enumerateColourings(const Graph &G, int k,
                             bool (*callback)(VertexLabeling<int>, T *param), T *callbackParam,
                             VertexLabeling<int> precolouring = VertexLabeling<int>(-1),
                             int maxColourings = -1)
    {
#ifdef BA_GRAPH_DEBUG
        assert(k >= 0);
#endif
        if (G.order() == 0) {
            if (callback != NULL) {
                VertexLabeling<int> vc(-1);
                callback(vc, callbackParam);
            }
            return true;
        }
        this->G = &G;
        this->k = k;
        this->callback = callback;
        this->callbackParam = callbackParam;
        this->maxColourings = maxColourings;

        colouring = std::vector<int>(max_number(G).to_int() + 1, noColour);
        if (!computeOrdering(precolouring))
            return false;
        foundColouringsCount = 0;
        doContinue = true;

        return colour(precolouredCount); // we only colour vertices not given a colour
    }
};

} // namespace internal

template <typename P>
bool enumerate_colourings_basic(const Graph &G, int k,
                                bool (*callback)(VertexLabeling<int>, P *param), P *callbackParam,
                                VertexLabeling<int> precolouring = VertexLabeling<int>(-1))
{
    internal::ColouringEnumerator<P> ce;
    return ce.enumerateColourings(G, k, callback, callbackParam, precolouring);
}

namespace internal
{

template <typename P>
struct EnumerateEdgeColouringsCallbackData
{
    const Graph *G;
    bool (*originalCallback)(EdgeLabeling<int>, P *param);
    P *originalCallbackParam;
    EdgeLabeling<Vertex> *edgeToVertex;
};

template <typename P>
bool enumerateEdgeColouringsCallback(VertexLabeling<int> lgColouring,
                                     EnumerateEdgeColouringsCallbackData<P> *data)
{
    EdgeLabeling<int> edgeColouring(-1);
    for (Edge e : data->G->list(RP::all(), IP::primary(), IT::e()))
        edgeColouring.set(e, lgColouring[(*(data->edgeToVertex))[e]]);
    return data->originalCallback(edgeColouring, data->originalCallbackParam);
}

} // namespace internal

template <typename P>
bool enumerate_edge_colourings_basic(const Graph &G, int k,
                                     bool (*callback)(EdgeLabeling<int>, P *param), P *callbackParam,
                                     EdgeLabeling<int> precolouring = EdgeLabeling<int>(-1))
{
    Factory f;
    auto [H, edgeToVertexNumber] = line_graph_with_map(G, f);
    VertexLabeling<int> lgPrecolouring(-1);
    for (Edge e : G.list(RP::all(), IP::primary(), IT::e()))
        lgPrecolouring.set(H[edgeToVertexNumber[e]].v(), precolouring[e]);
    EdgeLabeling<Vertex> edgeToVertex;
    for (Edge e : G.list(RP::all(), IP::primary(), IT::e()))
        edgeToVertex.set(e, H[edgeToVertexNumber[e]].v());
    struct internal::EnumerateEdgeColouringsCallbackData<P> data;
    data.G = &G;
    data.originalCallback = callback;
    data.originalCallbackParam = callbackParam;
    data.edgeToVertex = &edgeToVertex;
    return enumerate_colourings_basic(H, k, internal::enumerateEdgeColouringsCallback, &data, lgPrecolouring);
}

inline bool is_colourable_basic(const Graph &G, int k,
                         VertexLabeling<int> precolouring)
{
    internal::ColouringEnumerator<> ce;
    return ce.enumerateColourings(G, k, NULL, NULL, precolouring, 1);
}

inline bool is_colourable_basic(const Graph &G, int k, bool precolour = true)
{
    VertexLabeling<int> precolouring(-1);
    if (precolour) {
        if (G.size() >= 1) {
            if (k == 0)
                return false;
            Edge e = G.find(RP::all(), IP::all()).second->e();
            precolouring.set(e.v1(), 0);
            if (k >= 2)
                precolouring.set(e.v2(), 1);
            else
                return false;
        }
    }
    internal::ColouringEnumerator<> ce;
    return ce.enumerateColourings(G, k, NULL, NULL, precolouring, 1);
}

inline bool is_edge_colourable_basic(const Graph &G, int k,
                              EdgeLabeling<int> precolouring)
{
    if (has_loop(G))
        return false;
    Factory f;
    auto [H, edgeToVertex] = line_graph_with_map(G, f);
    VertexLabeling<int> lgPrecolouring(-1);
    for (Edge e : G.list(RP::all(), IP::primary(), IT::e()))
        lgPrecolouring.set(H[edgeToVertex[e]].v(), precolouring[e]);
    return is_colourable_basic(H, k, lgPrecolouring);
}

inline bool is_edge_colourable_basic(const Graph &G, int k, bool precolour = true)
{
    if (has_loop(G))
        return false;
    Factory f;
    auto [H, edgeToVertex] = line_graph_with_map(G, f);
    VertexLabeling<int> lgPrecolouring(-1);
    if (precolour) {
        int d = max_deg(G);
        if (k < d)
            return false;
        for (auto &r : G) {
            if (r.contains(r.n())) // there is a loop in G
                return false;
            if (r.degree() == d) {
                int c = 0;
                for (Edge e : r.list(IP::all(), IT::e()))
                    lgPrecolouring. set(H[edgeToVertex[e]].v(), c++);
                break;
            }
        }
    }
    return is_colourable_basic(H, k, lgPrecolouring);
}

inline int chromatic_number_basic(const Graph &g)
{
    for (int k = g.order() - 1; k >= 0; k--) {
        if (!is_colourable_basic(g, k))
            return k + 1;
    }
    return 0;
}

inline int chromatic_index_basic(const Graph &G)
{
    if (has_loop(G))
        return -1;
    for (int k = 0; k <= G.size(); ++k)
    {
        if (is_edge_colourable_basic(G, k))
            return k;
    }
    return -1;
}

template <typename P = void>
class BasicColouriser
{
  public:
    bool isColourable(const Graph &G) const
    {
        return is_edge_colourable_basic(G, 3, true);
    }

    bool isColourable(const Graph &G,
                      EdgeLabeling<int> precolouring) const
    {
        return is_edge_colourable_basic(G, 3, precolouring);
    }

    bool enumerateColourings(const Graph &G,
                             bool (*callback)(EdgeLabeling<int>, P *param), P *callbackParam,
                             EdgeLabeling<int> precolouring = EdgeLabeling<int>(-1)) const
    {
        return enumerate_edge_colourings_basic(G, 3, callback, callbackParam, precolouring);
    }
};

} // namespace ba_graph

#endif
