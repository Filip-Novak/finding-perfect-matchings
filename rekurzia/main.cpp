
#include <cstdlib>
#include <iostream>
#include <stdlib.h>
#include <math.h>
#include <vector>
#include <algorithm>
#include <string.h>
#include <set>
#include <ctime> 
#include <chrono>//
#include <fstream>//

#include <basic_impl.hpp>
#include <io.hpp>//
#include <sat/solver_bddmsat.hpp>//
#include <sat/exec_factors.hpp>//

using namespace ba_graph;

void timer(auto t) {
	/*std::cout << "Elapsed time in nanoseconds : " 
	<< std::chrono::duration_cast<std::chrono::nanoseconds>(t).count()
        << " ns" << std::endl;*/
 
	std::cout << "Elapsed time in microseconds : " 
        << std::chrono::duration_cast<std::chrono::microseconds>(t).count()
        << " µs" << std::endl;
 
	std::cout << "Elapsed time in milliseconds : " 
        << std::chrono::duration_cast<std::chrono::milliseconds>(t).count()
        << " ms" << std::endl;
 
	/*std::cout << "Elapsed time in seconds : " 
        << std::chrono::duration_cast<std::chrono::seconds>(t).count()
        << " sec" << std::endl;*/
}

double determinant(std::vector<std::vector<double>> matrix) {	//pocitanie determinantu matice pomocou Gaussovej eliminacie
    int n = matrix.size();
    double det = 1;

    for (int i = 0; i < n; i++) {

        double pivotElement = matrix[i][i];
        int pivotRow = i;
        for (int j = i + 1; j < n; j++) {
            if (std::abs(matrix[j][i]) > std::abs(pivotElement)) {
                pivotElement = matrix[j][i];
                pivotRow = j;
            }
        }
        if (pivotElement == 0.0) {
            return 0.0;
        }
        if (pivotRow != i) {
            matrix[i].swap(matrix[pivotRow]);
            det *= -1.0;
        }
        det *= pivotElement;

        for (int j = i + 1; j < n; j++) {
            for (int k = i + 1; k < n; k++) {
                matrix[j][k] -= matrix[j][i] * matrix[i][k] / pivotElement;
            }
        }
    }
    return det;
}

bool has_perfect_matching(int n, std::vector<Location> inM, std::set<Location> inE){

	std::vector<std::vector<double>> tutteMatrix (n, std::vector<double> (n));    //Tutteho matica, budeme z nej zistovat ci este ex. perf. parenie
	int m = n*n;
	int r_num;
	srand((unsigned)time(0));

	for (auto edge : inM) {
		r_num = (rand() % m) + 1;

		tutteMatrix[edge.n1().to_int()][edge.n2().to_int()]=r_num;
		tutteMatrix[edge.n2().to_int()][edge.n1().to_int()]=-r_num;
	}
	for (auto edge : inE) {
		r_num = (rand() % m) + 1;

		tutteMatrix[edge.n1().to_int()][edge.n2().to_int()]=r_num;
		tutteMatrix[edge.n2().to_int()][edge.n1().to_int()]=-r_num;
	}

	double res = determinant(tutteMatrix);
	if(res != 0) {
		return true;
	} else {
		return false;
	}
}

void remove_neighbours(std::vector<std::vector<Number>> &adj_list, std::set<Location> &edges_to_remove, Number u, Number v) {

    	std::vector<Number> u_neighbours = adj_list[u.to_int()];
	int n_i;
	
	for (auto neighbour : u_neighbours) {			//hladame a ukladame si hrany do edges_to_remove, ktore su susedmi zhladiska prveho vrcholu hrany "e",
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

void recursion(int n, std::vector<std::vector<Number>> &adj_list, std::set<Location> E, std::vector<Location> M, std::function<void(std::vector<Location> &, int *)> callback, int *callbackParam, int order) {

    if (M.size()*2 != n) {
        if (E.size() >= 1) {
	    
	    bool canContinue = true;
	    int percentage = round((M.size()*100) / (n/2));
	    if(percentage%10==0){						//po 10%
		if(!has_perfect_matching(n, M, E)){				//ma to perfektne parenie ?
			canContinue = false;	
		}
	    } 

	    if(canContinue){
		    std::set<Location> edges_to_remove;              		//pomocny set v ktorom si budeme pamatat hrany, ktore budeme vymazavat pred prvou rekurziu,
		                                                                //a nasledne tento set pouzijeme aby sme dostali nase mnoziny do zaciatocneho stavu

				
		    Location e;						//striedave vyberanie
		    Number v1, v2;
		    if ((order%2) == 0) {
			e = *std::next(E.begin(), 0);
		    	v1 = e.n1();
		    	v2 = e.n2();
			
			order++;
		    } else {
			e = *std::next(E.begin(), E.size()-1);
		    	v1 = e.n1();
		    	v2 = e.n2();

			order++;
		    }
		    /*Location e = *std::next(E.begin(), 0);         //normalne vyberanie
		    Number v1 = e.n1();
		    Number v2 = e.n2();*/

		    M.push_back(e);
		    edges_to_remove.insert(e);                                  //chceme odstranit z E aj hranu co je v perfektnom pareni, pridame ju do edges_to_remove
		    remove_neighbours(adj_list, edges_to_remove, v1, v2);
		    remove_neighbours(adj_list, edges_to_remove, v2, v1);

		    for(int i = 0; i < adj_list.size(); i++){			///lokalna podmienka, kde zistujeme ci je nejaky vrchol z ktoreho ide jedna hrana, potom tato hrana bude v perfektnom pareni
			if(adj_list[i].size() == 1){
				if(i <= adj_list[i][0].to_int()){
					M.push_back(Location(Number(i), adj_list[i][0]));
					edges_to_remove.insert(Location(Number(i), adj_list[i][0])); 
				} else {
					M.push_back(Location(adj_list[i][0], Number(i)));
					edges_to_remove.insert(Location(adj_list[i][0], Number(i)));
				}
				remove_neighbours(adj_list, edges_to_remove, adj_list[i][0], Number(i));
				adj_list[i].clear();
			}
		    } 

		    for (auto edge : edges_to_remove) {                         //odstranujeme hrany z E
		        auto pos = E.find(edge);
		        E.erase(pos);
		    }

		    recursion(n, adj_list, E, M, callback, callbackParam, order);

		    //------------------------------------------------------------------------------------  

		    std::vector<Location>::iterator itr = std::find(M.begin(), M.end(), e);	//chceme z M odstranit aj tie hrany, ktore sme pridali v lokalnej podmienke
    		    M.erase(itr, M.end()); 
		    //M.pop_back();
		    auto pos = edges_to_remove.find(e);
		    edges_to_remove.erase(pos);

		    for (auto edge : edges_to_remove) {                         //vratenie do zaciatocneho stavu ale bez hrany "e" lebo sme ju vyhodili v prikaze vyssie
		        E.insert(edge);
		        adj_list[edge.n1().to_int()].push_back(edge.n2());
		        adj_list[edge.n2().to_int()].push_back(edge.n1());
		    }                                                           //ked skonci for cyklus, tak je to pripravene na rekurziu
				
		    recursion(n, adj_list, E, M, callback, callbackParam, order);
				
		    adj_list[v1.to_int()].push_back(v2);		//vratenie adj_list do zaciatocneho stavu
		    adj_list[v2.to_int()].push_back(v1);
	    }
        }
    } else {
	callback(M, callbackParam);
    }
}

void p_m_counter(std::vector<Location> &, int *count) { 	//callback: moja funkcia pre rekurziu
    (*count)++;
}

bool cb1f(std::vector<Edge> &perfectMatching, int *count) {
    perfectMatching = perfectMatching;
    (*count)++;
    return true;
}   

void perfect_matchings_recursion(Graph &G) {

    int n = G.order();						//pocet vrcholov	
    std::vector<Location> M;                                 	//M je mnozina hran(perfektne parenie)
    std::set<Location> E;                                    	//mnozina hran v grafe
    std::vector<std::vector<Number>> adj_list(n);		//pre kazdy vrchol mame zaznamenane vrcholy, ktore s nim susedia
	
	Number vertex, v, u;
	Location e;

 
    for (auto &r : G) {						//inicializacia E a adj_list
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
	
	int order=0;//////
	int c = 0;//
	recursion(n, adj_list, E, M, p_m_counter, &c, order);///
	
	std::cout << "Recursion:" << c << std::endl;//			//pocet perf. par.
}

int main(int argc, char** argv) {

	/*std::string s = ":g_OGCEBA`Ow[QHDapgs]NGcQXKg[QdCHW}VKFRA@QYNesQXebQMsrdOpTKfYl\AclFsd|?a";		//priklad grafu
	Graph g(read_graph6_line(s));//

	auto start = std::chrono::steady_clock::now();//
	perfect_matchings_recursion(g);					//pouzitie rekurzie
	auto end = std::chrono::steady_clock::now();//
	
	auto t = end - start;
	timer(t);

   	std::cout << std::endl;//---------------------------------------------------------------------
		
	Configuration cfg;
	cfg.load_from_string(R"delim({
        "storage": {
            "dir": "../../resources/graphs"
        },
        "allsat_solvers": [
            {
                "output_type": "BDD_MINISAT",
                "execute_command": "/home/filip/Desktop/Bakalarka/rekurzia/bdd_minisat_all-1.0.2/bdd_minisat_all_static"
            }
        ]
    	})delim");

    	AllSatSolver solver(cfg, 0);
	int c = 0;
	
	auto start2 = std::chrono::steady_clock::now();//
	perfect_matchings_enumerate_sat(solver, g, cb1f, &c);		//pouzitie sat solvera
	auto end2 = std::chrono::steady_clock::now();//
	
	std::cout << "AllSatSolver:" << c << std::endl;
	t = end2 - start2;
	timer(t);*/




	std::ifstream infile("100-kubi_grafov.txt");///////

		Configuration cfg;
		cfg.load_from_string(R"delim({
		"storage": {
		    "dir": "../../resources/graphs"
		},
		"allsat_solvers": [

		    {
		        "output_type": "BDD_MINISAT",

		        "execute_command": "/home/filip/Desktop/Bakalarka/rekurzia/bdd_minisat_all-1.0.2/bdd_minisat_all_static"
		    }
		]
	    	})delim");

	    	AllSatSolver solver(cfg, 0);

	std::set<double> med;
	double median;    
	int min=INT_MAX;
	unsigned long long int max=0;
	double mean; 	//priemer
	double sum=0.0;
	double temp_num;
	std::string s;/////

	while (infile >> s)/////
	{
		Graph g(read_graph6_line(s));///////

		auto start = std::chrono::steady_clock::now();//
		perfect_matchings_recursion(g);					//pouzitie rekurzie
		auto end = std::chrono::steady_clock::now();//
		
		auto t = end - start;
		timer(t);



		int c = 0;	

		auto start2 = std::chrono::steady_clock::now();//
		perfect_matchings_enumerate_sat(solver, g, cb1f, &c);		//pouzitie sat solvera
		auto end2 = std::chrono::steady_clock::now();//
		
		std::cout << "AllSatSolver:" << c << std::endl;
		auto t2 = end2 - start2;
		timer(t2);


		temp_num = std::chrono::duration_cast<std::chrono::microseconds>(t).count(); //t
		if(min > temp_num) {
			min = temp_num;
		}
		if(max < temp_num){
			max=temp_num;
		}
		sum += temp_num;
		med.insert(temp_num);
	}////

	mean = sum / 100;
	double x = *std::next(med.begin(), 49);
	double y = *std::next(med.begin(), 50);
	median = (x + y) / 2;
	std::cout << "Min: " << min << " microseconds" << std::endl;
	std::cout << "Max: " << max << " microseconds" << std::endl;
	std::cout << "Priemer: " << mean << " microseconds" << std::endl;
	std::cout << "Median: " << median << " microseconds" << " " << x << " " << y << std::endl;

	return 0; 
}

