FSTAR_HOME=..
include ../examples/Makefile.include

ALL_TEST_DIRS=\
bug-reports \
friends \
incl \
machine_integers \
micro-benchmarks \
struct

all: $(addsuffix .all, $(ALL_TEST_DIRS))

%.all: %
	+$(MAKE) -C $^ all

test: all

clean:
	rm ../cache/*.cache
