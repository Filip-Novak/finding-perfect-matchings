PREFIX = ../..

include $(PREFIX)/makerc

CXXFLAGS = $(DEFAULT_CXXFLAGS) -I$(NAUTY_INCLUDE_PATH)
DBGFLAGS = $(DEFAULT_DBGFLAGS)
LDFLAGS = $(DEFAULT_LDFLAGS) -L$(NAUTY_LIB_PATH)
LDLIBS = $(DEFAULT_LDLIBS) -lnauty

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
