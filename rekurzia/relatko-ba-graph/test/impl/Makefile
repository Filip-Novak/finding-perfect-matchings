DBGFLAGS = -g -O0 -fconcepts -pedantic -Wall -Wextra -DBA_GRAPH_DEBUG -D_GLIBCXX_DEBUG
CFLAGS = -std=c++17 $(DBGFLAGS)


all: swap_to_basic test1 test2 test3 test4 test5 test6 test7

swap_to_basic:
	cp implementation_basic.h implementation.h

compile: compile1 compile2 compile3 compile4 compile5 compile6 compile7


test1: compile1
	./01.out
compile1:
	$(CXX) $(CFLAGS) 01vertices_edges_halfedges.cpp -o 02.out

test2: compile2
	./02.out
compile2:
	$(CXX) $(CFLAGS) 02creating_deleting_graph.cpp -o 02.out

test3: compile3
	./03.out
compile3:
	$(CXX) $(CFLAGS) 03basic_graph_traversals.cpp -o 03.out

test4: compile4
	./04.out
compile4:
	$(CXX) $(CFLAGS) 04searching.cpp -o 04.out

test5: compile5
	./05.out
compile5:
	$(CXX) $(CFLAGS) 05graph_constructing_functions.cpp -o 05.out

test6: compile6
	./06.out
compile6:
	$(CXX) $(CFLAGS) 06mappings.cpp -o 06.out

test7: compile7
	./07.out
compile7:
	$(CXX) $(CFLAGS) 07renumbering.cpp -o 07.out


clean:
	rm -rf *.out


.PHONY: clean all compile test1 compile1 test2 compile2 test3 compile3 test4 compile4 test5 compile5 test6 compile6 test7 compile7
