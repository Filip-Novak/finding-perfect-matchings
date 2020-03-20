
#include <cstdlib>
#include <iostream>
#include <stdlib.h>
#include <math.h>
#include <vector>
#include <algorithm>
#include <string.h>
#include <set> 

#include <basic_impl.hpp>

using namespace std;
using namespace ba_graph;

void remove_neighbours(vector<vector<int>>& adj_list, set<pair<int, int>>& edges_to_remove, int u, int v) {
	
    vector<int> u_neighbours = adj_list[u];

    for (int i = 0; i < u_neighbours.size(); i++) {                      //hladame a ukladame si hrany do edges_to_remove, ktore su susedmi zhladiska prveho vrcholu hrany "e",
                                                                         //nasledne vymazavame v adj_list vrcholy tych hran 
        if (u_neighbours[i] != v) {
            if (u <= u_neighbours[i]) {
                edges_to_remove.insert(make_pair(u, u_neighbours[i]));
            } else {
                edges_to_remove.insert(make_pair(u_neighbours[i], u));
            }
            adj_list[u_neighbours[i]].erase(remove(adj_list[u_neighbours[i]].begin(), adj_list[u_neighbours[i]].end(), u), adj_list[u_neighbours[i]].end());
        }
    }
    adj_list[u].clear();
}

void recursion(int n, vector<vector<int>> adj_list, set<pair<int, int>> E, vector<pair<int, int>> M) {
    
    if (M.size()*2 != n) { 
        if (E.size() >= 1) {
            set<pair<int, int>> edges_to_remove;                    	//pomocny set v ktorom si budeme pamatat hrany, ktore budeme vymazavat pred prvou rekurziu,
																		//a nasledne tento set pouzijeme aby sme dostali nase mnoziny do zaciatocneho stavu
			pair<int, int> e = *next(E.begin(), 0);
            int v1 = e.first;
            int v2 = e.second;
			
            M.push_back(e);
			edges_to_remove.insert(e);									//chceme odstranit z E aj hranu co je v perfektnom pareni, tak ju pridame do edges_to_remove
            remove_neighbours(adj_list, edges_to_remove, v1, v2);
            remove_neighbours(adj_list, edges_to_remove, v2, v1);

            for (auto edge : edges_to_remove) { 						//odstranujeme hrany z E
				auto pos = E.find(edge);
				E.erase(pos);
            }  
            recursion(n, adj_list, E, M);

            //------------------------------------------------------------------------------------  

            M.pop_back();
            auto pos = edges_to_remove.find(e);
            edges_to_remove.erase(pos);

            for (auto edge : edges_to_remove) {							//vratenie do zaciatocneho stavu ale bez hrany "e" lebo sme ju vyhodili v prikaze vyssie
				E.insert(edge);
                adj_list[edge.first].push_back(edge.second);
                adj_list[edge.second].push_back(edge.first);
            }                                                           //ked skonci for cyklus, tak je to pripravene na rekurziu
            recursion(n, adj_list, E, M);
       }
    } else {
		callback(M);
    } 
}

void perfect_matchings_recursion(Graph &G){
	
	int n = G.order();  												//pocet vrcholov	
	vector<pair<int, int>> M;            								//M je mnozina hran(perfektne parenie)
    set<pair<int, int>> E;			    			    				//mnozina hran v grafe
    vector<vector<int>> adj_list(n);        							//pre kazdy vrchol mame zaznamenane vrcholy, ktore s nim susedia
	
	for (auto &vertex : G) {											//inicializacia E a adj_list
		Number v = vertex.n();
		for (auto u : G[v].neighbours()) {
			if (v <= u) {
				E.insert(make_pair(v.to_int(), u.to_int()));
			}else{
				E.insert(make_pair(u.to_int(), v.to_int()));
			}
			adj_list[v.to_int()].push_back(u.to_int());			
		}
	}	
	recursion(n, adj_list, E, M);
}

int main(int argc, char** argv) { 

	Graph g(createG());			//priklad grafu
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
