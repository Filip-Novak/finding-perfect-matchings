#ifndef BA_GRAPH_SAT_EXEC_FACTORS_HPP
#define BA_GRAPH_SAT_EXEC_FACTORS_HPP

#include "cnf_factors.hpp"
#include "exec_solver.hpp"
#include "solver.hpp"

#include "../invariants/degree.hpp"
#include "../operations/copies.hpp"

namespace ba_graph
{

inline bool has_perfect_matching_sat(const SatSolver &solver, const Graph &G)
{
    auto cnf = cnf_perfect_matching(G);
    return satisfiable(solver, cnf);
}

template <typename P>
bool perfect_matchings_enumerate_sat(const AllSatSolver &solver, const Graph &G,
        bool (*callback)(std::vector<Edge> &perfectMatching, P *param), P *callbackParam)
{
    auto cnf = cnf_perfect_matching(G);
    return all_sat_solutions(solver, cnf, callback, callbackParam,
        internal::transform_to_perfect_matching, &G);
}

inline std::vector<std::vector<Edge>>
perfect_matchings_list_sat(const AllSatSolver &solver, const Graph &G)
{
    std::vector<std::vector<Edge>> list;
    perfect_matchings_enumerate_sat(solver, G, enumerateListCallback, &list);
    return list;
}

inline bool has_kfactor_sat(const SatSolver &solver, const Graph &G, int k)
{
    auto cnf = cnf_kfactor(G, k);
    return satisfiable(solver, cnf);
}

template <typename P>
bool kfactors_enumerate_sat(const AllSatSolver &solver, const Graph &G, int k, Factory &f,
        bool (*callback)(Graph &kfactor, P *param), P *callbackParam)
{
    auto cnf = cnf_kfactor(G, k);
    struct internal::KFactorTransformData data;
    data.G = &G;
    data.f = &f;
    return all_sat_solutions(solver, cnf, callback, callbackParam,
        internal::transform_to_kfactor, &data);
}

inline std::vector<Graph>
kfactors_list_sat(const AllSatSolver &solver, const Graph &G, int k, Factory &f)
{
    std::vector<Graph> list;
    kfactors_enumerate_sat(solver, G, k, f, enumerateListCallback, &list);
    return list;
}


/*
 * ====================== 2-factors for cubic graphs via allsat =======================
 */

namespace internal
{

inline Graph transform_to_2factor_cubic(std::vector<bool> &solution, struct KFactorTransformData *data)
{
    Graph F(copy_identical(*data->G, *data->f));
    auto pmEdges = transform_to_perfect_matching(solution, data->G);
    for (auto e : pmEdges)
        deleteE(F, e, *data->f);
    return F;
}


} // namespace internal

template <typename P>
bool two_factors_enumerate_allsat_cubic(const AllSatSolver &solver, const Graph &G, Factory &f,
        bool (*callback)(Graph &F, P *param), P *callbackParam)
{
#ifdef BA_GRAPH_DEBUG
    assert(max_deg(G) == 3);
    assert(min_deg(G) == 3);
#endif
    auto cnf = cnf_perfect_matching(G);
    struct internal::KFactorTransformData data;
    data.G = &G;
    data.f = &f;
    return all_sat_solutions(solver, cnf, callback, callbackParam,
            internal::transform_to_2factor_cubic, &data);
}

inline std::vector<Graph> two_factors_list_allsat_cubic(const AllSatSolver &solver, const Graph &G, Factory &f)
{
#ifdef BA_GRAPH_DEBUG
    assert(max_deg(G) == 3);
    assert(min_deg(G) == 3);
#endif
    std::vector<Graph> list;
    two_factors_enumerate_allsat_cubic(solver, G, f, enumerateListCallback, &list);
    return list;
}

}  // namespace end

#endif

