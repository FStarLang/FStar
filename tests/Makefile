FSTAR_HOME=..
include ../examples/Makefile.include

ALL_TEST_DIRS=\
bug-reports \
error-messages \
friends \
incl \
interactive \
machine_integers \
micro-benchmarks \
prettyprinting \
struct \
tactics

all: $(addsuffix .all, $(ALL_TEST_DIRS))
clean: $(addsuffix .clean, $(ALL_TEST_DIRS))

%.all: %
	+$(MAKE) -C $^ all

%.clean: %
	+$(MAKE) -C $^ clean
