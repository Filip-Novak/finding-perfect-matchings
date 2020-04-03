PREFIX = ..

include $(PREFIX)/makerc

CXXFLAGS = $(DEFAULT_CXXFLAGS)
DBGFLAGS = $(DEFAULT_DBGFLAGS)
LDFLAGS = $(DEFAULT_LDFLAGS)
LDLIBS = $(DEFAULT_LDLIBS)

COMPILE_DBG = $(CXX) $(CXXFLAGS) $(DBGFLAGS) $(LDFLAGS)

TEST_FILES := $(wildcard test_*.cpp)
SUBDIRS = $(wildcard */.)


all: swap_to_basic $(patsubst test_%.cpp, run_%, $(TEST_FILES))
	@for d in $(SUBDIRS); do \
		echo "============================== $$d =============================="; \
		$(MAKE) -C "$$d" all; \
	done

swap_to_basic:
	cp $(PREFIX)/implementation_basic.h implementation.h
	@for d in $(SUBDIRS); do \
		echo "============================== $$d =============================="; \
		$(MAKE) -C "$$d" swap_to_basic; \
	done

compile: $(patsubst test_%.cpp, test_%.out, $(TEST_FILES))
	@for d in $(SUBDIRS); do \
		echo "============================== $$d =============================="; \
		$(MAKE) -C "$$d" compile; \
	done

run: $(patsubst test_%.cpp, run_%, $(TEST_FILES))
	@for d in $(SUBDIRS); do \
		echo "============================== $$d =============================="; \
		$(MAKE) -C "$$d" run; \
	done

test_%.out: test_%.cpp
	@echo "------------------------------ $< ------------------------------"
	$(COMPILE_DBG) $< -o $@ $(LDLIBS)

run_%: test_%.out
	./$<

clean:
	rm -rf *.out
	$(MAKE) -C object_collection clean
	$(MAKE) -C path_decomposition clean
	$(MAKE) -C isomorphism clean


.PHONY: clean all compile run swap_to_basic
