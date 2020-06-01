CFLAGS = -std=c++17 -fconcepts -I/home/filip/Desktop/Bakalarka/rekurzia/ba-graph/include
#LDFLAGS = -lcryptominisat5
LDFLAGS =
DBGFLAGS = -g -O0 -pedantic -Wall -Wextra -DBA_GRAPH_DEBUG
COMPILE_DBG = $(CXX) $(CFLAGS) $(DBGFLAGS)
COMPILE = $(CXX) $(CFLAGS) -DNDEBUG -O3

all: recursion


recursion:
	$(COMPILE) main.cpp -o recursion $(LDFLAGS)

recursion_dbg:
	$(COMPILE_DBG) main.cpp -o recursion $(LDFLAGS)


clean:
	rm -rf *.out


.PHONY: clean all recursion recursion_dbg
