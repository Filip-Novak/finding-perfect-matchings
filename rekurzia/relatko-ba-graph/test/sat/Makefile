PREFIX = ..

include $(PREFIX)/makerc

CXXFLAGS = $(DEFAULT_CXXFLAGS) -I$(CRYPTOMINISAT_INCLUDE_PATH)
DBGFLAGS = -g -O0 -pedantic -Wall -Wextra -DBA_GRAPH_DEBUG
# cannot use -D_GLIBCXX_DEBUG because of cryptominisat
LDFLAGS = $(DEFAULT_LDFLAGS) -L$(CRYPTOMINISAT_LIB_PATH)
LDLIBS = $(DEFAULT_LDLIBS) -lcryptominisat5

COMPILE_DBG = $(CXX) $(CXXFLAGS) $(DBGFLAGS) $(LDFLAGS)

TEST_FILES := $(wildcard test_*.cpp)


all: swap_to_basic $(patsubst test_%.cpp, run_%, $(TEST_FILES))

swap_to_basic:
	cp $(PREFIX)/implementation_basic.h implementation.h

compile: $(patsubst test_%.cpp, test_%.out, $(TEST_FILES))

run: $(patsubst test_%.cpp, run_%, $(TEST_FILES))

test_%.out: test_%.cpp
	@echo "------------------------------ $< ------------------------------"
	$(COMPILE_DBG) $< -o $@ $(LDLIBS)

run_%: test_%.out
	./$<

clean:
	rm -rf *.out


.PHONY: clean all compile run swap_to_basic
