#include <cstdlib>
#include <iostream>
#include <stdlib.h>
#include <math.h>
#include <vector>
#include <algorithm>
#include <string.h>
#include <set>
#include <ctime> 
#include <chrono>
#include <fstream>

#include <basic_impl.hpp>
#include <io.hpp>

using namespace ba_graph;

void timer(auto t) {

    std::cout << "Elapsed time in microseconds : "
            << std::chrono::duration_cast<std::chrono::microseconds>(t).count()
            << " µs" << std::endl;

    std::cout << "Elapsed time in milliseconds : "
            << std::chrono::duration_cast<std::chrono::milliseconds>(t).count()
            << " ms" << std::endl;
}

std::vector<std::vector<int>> get_adj_matrix(int n, std::set<Location> E) {

    std::vector<std::vector<int>> matrix(n, std::vector<int> (n));
    int v1, v2;

    for (auto edge : E) {

        v1 = edge.n1().to_int();
        v2 = edge.n2().to_int();

        matrix[v1][v2] = 1;
        matrix[v2][v1] = 1;
    }
    return matrix;
}

//implementacia programu s Tutteho maticou
float determinant(std::vector<std::vector<float>> matrix, int n) { //pocitanie determinantu matice pomocou Gaussovej eliminacie
                                                                    //https://codereview.stackexchange.com/questions/204135/determinant-using-gauss-elimination

    float det = 1;

    for (int i = 0; i < n; i++) {

        float pivotElement = matrix[i][i];
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

bool tutte_matrix(int n, std::set<Location> E) {

    std::vector<std::vector<float>> tutteMatrix(n, std::vector<float> (n)); //Tutteho matica, budeme z nej zistovat ci este ex. perf. parenie
    int m = n*n;
    int r_num;
    srand((unsigned) time(0));

    int v1, v2;
    for (auto edge : E) {
        r_num = (rand() % m) + 1;

        v1 = edge.n1().to_int();
        v2 = edge.n2().to_int();

        tutteMatrix[v1][v2] = r_num;
        tutteMatrix[v2][v1] = -r_num;
    }

    float res = determinant(tutteMatrix, n);
    if (res != 0) {
        return true;
    } else {
        return false;
    }
}

//implementacia zrýchleného Rabin-Vaziraniho algoritmu
void getCofactor(std::vector<std::vector<float>> &matrix, std::vector<std::vector<float>> &temp, int p, int q, int n) {
    int i = 0, j = 0;

    for (int row = 0; row < n; row++) {
        for (int col = 0; col < n; col++) {
            if (row != p && col != q) {
                temp[i][j++] = matrix[row][col];

                if (j == n - 1) {
                    j = 0;
                    i++;
                }
            }
        }
    }
}

std::vector<std::vector<float>> adjoint(int n, std::vector<std::vector<float>> matrix) {

    std::vector<std::vector<float>> adj(n, std::vector<float> (n));

    if (n == 1) {
        adj[0][0] = 1;
        return adj;
    }

    std::vector<std::vector<float>> temp(n, std::vector<float> (n));
    int sign = 1;

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            getCofactor(matrix, temp, i, j, n);

            sign = ((i + j) % 2 == 0) ? 1 : -1;

            adj[j][i] = (sign)*(determinant(temp, n - 1));
        }
    }
    return adj;
}

std::vector<std::vector<float>> inverseOfMatrix(int n, std::vector<std::vector<float>> matrix) { //inverzia matice pomocou adjoint, getCofactor a determinant(z implementacie Tutteho matice)
                                                                                                 //https://www.geeksforgeeks.org/adjoint-inverse-matrix/

    std::vector<std::vector<float>> invMatrix(n, std::vector<float> (n));

    float det = determinant(matrix, n);
    if (det == 0) {
        std::cout << "Singular matrix, can't find its inverse";
        std::vector<std::vector<float>> badInvMatrix;
        return badInvMatrix;
    }

    std::vector<std::vector<float>> adj = adjoint(n, matrix);

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            invMatrix[i][j] = adj[i][j] / det;
        }
    }

    return invMatrix;
}

std::vector<std::vector<float>> get_tutteMatrix(int n, std::vector<std::vector<int>> &graph_matrix) {

    std::vector<std::vector<float>> matrix(n, std::vector<float> (n));
    int m = n*n;
    int r_num;
    srand((unsigned) time(0));


    for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
            if (graph_matrix[i][j] != 0) {
                r_num = (rand() % m) + 1;

                matrix[i][j] = r_num;
                matrix[j][i] = -r_num;
            }
        }
    }

    return matrix;
}

Location find_edge_IRB(int n, int i, std::vector<std::vector<int>> graph_matrix, std::vector<std::vector<float>> inv_tutteMatrix) {

    for (int j = 0; j < n; j++) {
        if (graph_matrix[i][j] == 1 && inv_tutteMatrix[i][j] != 0) {
            return Location(Number(i), Number(j));
        }
    }
    return Location(Number(-1), Number(-1));
}

bool improved_Rabin_Vazirani(int n, std::vector<std::vector<int>> graph_matrix) {

    std::vector<Location> M; //M je mnozina hran (perfektne parenie)
    std::vector<std::vector<float>> tutteMatrix(n, std::vector<float> (n)); //Tutteho matica
    std::vector<std::vector<float>> inv_tutteMatrix(n, std::vector<float> (n)); //inverzia matice
    Location edge;
    int v1, v2;

    tutteMatrix = get_tutteMatrix(n, graph_matrix);
    inv_tutteMatrix = inverseOfMatrix(n, tutteMatrix);

    if (inv_tutteMatrix.size() == 0) {
        return false;
    }

    for (int i = 0; i < n; i++) {

        edge = find_edge_IRB(n, i, graph_matrix, inv_tutteMatrix);
        v1 = edge.n1().to_int();
        v2 = edge.n2().to_int();
        if (v1 == -1 && v2 == -1) {
            continue;
        }

        M.push_back(edge); //pridanie hrany do perfektneho parenia

        for (int j = 0; j < n; j++) { //odstranenie hran 
            graph_matrix[v1][j] = 0;
            graph_matrix[j][v1] = 0;
            graph_matrix[v2][j] = 0;
            graph_matrix[j][v2] = 0;

            inv_tutteMatrix[v1][j] = 0; //odstranenie riadkov a stlpcov z inverzie
            inv_tutteMatrix[j][v1] = 0;
            inv_tutteMatrix[v2][j] = 0;
            inv_tutteMatrix[j][v2] = 0;
        }
    }

    if (M.size()*2 == n) {
        return true;
    } else {
        return false;
    }
}

int main(int argc, char** argv) {

    std::set<double> med;
    double median;
    int min = INT_MAX;
    unsigned long long int max = 0;
    double mean; //priemer
    double sum = 0.0;
    double temp_num;
    std::string s;

    std::ifstream infile("26-kubi_grafov.txt"); //grafy na ktorých spustame algority

    while (infile >> s) {

        Graph g(read_graph6_line(s));


        int n = g.order(); //pocet vrcholov	
        std::set<Location> E; //mnozina hran v grafe
        std::vector<std::vector<int>> graph_matrix; //reprezentacia grafu

        Number vertex, v, u;
        Location e;

        for (auto &r : g) { //inicializacia E
            vertex = r.n();
            for (auto &i : g[vertex]) {
                v = i.n1();
                u = i.n2();
                e = i.l();

                if (v <= u) {
                    E.insert(e);
                } else {
                    E.insert(e.reverse());
                }
            }
        }
        graph_matrix = get_adj_matrix(n, E); //inicializacia grafu v 2D vektore

        //---------------------------------------------------------------------------------

        auto start = std::chrono::steady_clock::now();
        bool result = tutte_matrix(n, E); //pouzitie Tutteho matice
        auto end = std::chrono::steady_clock::now();

        std::cout << "Tutte matrix: " << result << std::endl;

        auto t = end - start;
        timer(t);

        //---------------------------------------------------------------------------------

        auto start2 = std::chrono::steady_clock::now();
        bool result2 = improved_Rabin_Vazirani(n, graph_matrix); //pouzitie zrycheleneho Rabin-Vaziraniho algoritmu
        auto end2 = std::chrono::steady_clock::now();

        std::cout << "Improved Rabin-Vazirani: " << result2 << std::endl;
        auto t2 = end2 - start2;
        timer(t2);


        temp_num = std::chrono::duration_cast<std::chrono::microseconds>(t).count(); //aktualne meriame cas programu s Tutteho maticou
        if (min > temp_num) {
            min = temp_num;
        }
        if (max < temp_num) {
            max = temp_num;
        }
        sum += temp_num;
        med.insert(temp_num);
    }

    mean = sum / 26; // 26 grafov
    double x = *std::next(med.begin(), 12);
    double y = *std::next(med.begin(), 13);
    median = (x + y) / 2;
    std::cout << "Min: " << min << " microseconds" << std::endl;
    std::cout << "Max: " << max << " microseconds" << std::endl;
    std::cout << "Priemer: " << mean << " microseconds" << std::endl;
    std::cout << "Median: " << median << " microseconds" << " " << x << " " << y << std::endl;

    return 0;
}

