
#include <cstdlib>
#include <iostream>
#include <stdlib.h>
#include <math.h>
#include <vector>
#include <algorithm>
#include <string.h>
#include <set> 

#include <basic_impl.hpp>

using namespace ba_graph;

void remove_neighbours(std::vector<std::vector<Number>> &adj_list, std::set<Location> &edges_to_remove, Number u, Number v) {

    std::vector<Number> u_neighbours = adj_list[u.to_int()];
	int n_i;
	
	for (auto neighbour : u_neighbours) {								//hladame a ukladame si hrany do edges_to_remove, ktore su susedmi zhladiska prveho vrcholu hrany "e",
																		//nasledne vymazavame v adj_list vrcholy tych hran 
		if (neighbour != v) {
			if (u <= neighbour) {
				edges_to_remove.insert(Location(u, neighbour));
			} else {
				edges_to_remove.insert(Location(neighbour, u));
			}
			n_i = neighbour.to_int();
			adj_list[n_i].erase(std::remove(adj_list[n_i].begin(), adj_list[n_i].end(), u), adj_list[n_i].end());
		}
    }
    adj_list[u.to_int()].clear();
}

void recursion(int n, std::vector<std::vector<Number>> adj_list, std::set<Location> E, std::vector<Location> M, std::function<void(std::vector<Location> &)> callback) {

    if (M.size()*2 != n) {
        if (E.size() >= 1) {
            std::set<Location> edges_to_remove;              			//pomocny set v ktorom si budeme pamatat hrany, ktore budeme vymazavat pred prvou rekurziu,
                                                                        //a nasledne tento set pouzijeme aby sme dostali nase mnoziny do zaciatocneho stavu
            Location e = *std::next(E.begin(), 0);
            Number v1 = e.n1();
            Number v2 = e.n2();

            M.push_back(e);
            edges_to_remove.insert(e);                                  //chceme odstranit z E aj hranu co je v perfektnom pareni, tak ju pridame do edges_to_remove
            remove_neighbours(adj_list, edges_to_remove, v1, v2);
            remove_neighbours(adj_list, edges_to_remove, v2, v1);

            for (auto edge : edges_to_remove) {                         //odstranujeme hrany z E
                auto pos = E.find(edge);
                E.erase(pos);
            }
            recursion(n, adj_list, E, M, callback);

            //------------------------------------------------------------------------------------  

            M.pop_back();
            auto pos = edges_to_remove.find(e);
            edges_to_remove.erase(pos);

            for (auto edge : edges_to_remove) {                         //vratenie do zaciatocneho stavu ale bez hrany "e" lebo sme ju vyhodili v prikaze vyssie
                E.insert(edge);
                adj_list[edge.n1().to_int()].push_back(edge.n2());
                adj_list[edge.n2().to_int()].push_back(edge.n1());
            }                                                           //ked skonci for cyklus, tak je to pripravene na rekurziu
            recursion(n, adj_list, E, M, callback);
        }
    } else {
		/*for (int i = 0; i < M.size(); i++) {
            std::cout << M[i].n1().to_int() << "-" << M[i].n2().to_int() << " ";
        }
        std::cout << std::endl;*/
		callback(M);
    }
}

void perfect_matchings_recursion(Graph &G) {

    int n = G.order();                                                  //pocet vrcholov	
    std::vector<Location> M;                                 			//M je mnozina hran(perfektne parenie)
    std::set<Location> E;                                    			//mnozina hran v grafe
    std::vector<std::vector<Number>> adj_list(n);						//pre kazdy vrchol mame zaznamenane vrcholy, ktore s nim susedia
	
	Number vertex, v, u;
	Location e;
    for (auto &r : G) {													//inicializacia E a adj_list
        vertex = r.n();
        for (auto &i : G[vertex]) {
			v = i.n1();
			u = i.n2();
			e = i.l();
			
            if (v <= u) {
                E.insert(e);
            } else {
                E.insert(e.reverse());
            }
			adj_list[v.to_int()].push_back(u);
        }
    }
	std::function<void(std::vector<Location> &)> callback;
    recursion(n, adj_list, E, M, callback);
}

int main(int argc, char** argv) {

    Graph g(createG());                                                 //priklad grafu
    addV(g, 0);
    addV(g, 1);
    addV(g, 2);
    addV(g, 3);
    addE(g, Location(0, 1));
    addE(g, Location(0, 3));
    addE(g, Location(1, 2));
    addE(g, Location(2, 3));
	
    perfect_matchings_recursion(g);
}
