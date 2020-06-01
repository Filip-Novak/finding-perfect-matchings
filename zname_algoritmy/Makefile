CFLAGS = -std=c++17 -fconcepts -I/home/filip/Desktop/Bakalarka/zname_algoritmy/ba-graph/include
#LDFLAGS = -lcryptominisat5
LDFLAGS =
DBGFLAGS = -g -O0 -pedantic -Wall -Wextra -DBA_GRAPH_DEBUG
COMPILE_DBG = $(CXX) $(CFLAGS) $(DBGFLAGS)
COMPILE = $(CXX) $(CFLAGS) -DNDEBUG -O3

all: algorithms


algorithms:
	$(COMPILE) main.cpp -o algorithms $(LDFLAGS)

algorithms_dbg:
	$(COMPILE_DBG) main.cpp -o algorithms $(LDFLAGS)


clean:
	rm -rf *.out


.PHONY: clean all algorithms algorithms_dbg
