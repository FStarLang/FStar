FSTAR_HOME=..
include ../examples/Makefile.include

ALL_TEST_DIRS=\
bug-reports \
friends \
incl \
interactive \
machine_integers \
micro-benchmarks \
prettyprinting \
struct

all: $(addsuffix .all, $(ALL_TEST_DIRS))

%.all: %
	+$(MAKE) -C $^ all

test: all

clean:
	rm ../cache/*.cache
