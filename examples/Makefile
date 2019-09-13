FSTAR_HOME=..
include Makefile.include

# Note: native_tactics is not included in the list below, it is called
# explicitly by the uexamples rule from the Makefile in ../src/Makefile.
# These examples are excluded since the binary package can't verify
# them.

ALL_EXAMPLE_DIRS=\
bug-reports \
data_structures \
algorithms \
crypto \
termination \
software_foundations \
maths \
rel \
paradoxes \
printf \
metatheory \
verifythis \
preorders \
dm4free \
incl \
struct \
micro-benchmarks \
friends \
tactics \
typeclasses \
miniparse \
kv_parsing \
low-mitls-experiments \
seplogic \
csl \
hello \
extraction \
demos \
refinement \
indexed_effects \
doublylinkedlist \
regional \
generic \
calc \
layeredeffects

# low-level \  ... NS: removing from CI for this branch

all: $(addsuffix .all, $(ALL_EXAMPLE_DIRS))

%.all: %
	+$(MAKE) -C $^ all

test: all

stdlib: $(addprefix ../lib/, FStar.List.fst FStar.String.fsti partialmap.fst FStar.ST.fst)
	mkdir -p ../cache
	$(FSTAR) $^ --serialize_mods

clean:
	rm ../cache/*.cache

wc:
	find . -name "*.fst" | grep -v -e to_be_ported | xargs sloccount
