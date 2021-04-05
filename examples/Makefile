include Makefile.include

# Note: native_tactics is not included in the list below, it is called
# explicitly by the uexamples rule from the Makefile in ../src/Makefile.
# These examples are excluded since the binary package can't verify
# them.

ALL_EXAMPLE_DIRS_NO_KREMLIN=\
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
tactics \
param \
typeclasses \
low-mitls-experiments \
seplogic \
csl \
hello \
extraction \
demos \
indexed_effects \
doublylinkedlist \
regional \
generic \
calc \
steel \
layeredeffects \
misc

ifdef KREMLIN_HOME
ALL_EXAMPLE_DIRS=\
  kv_parsing \
  miniparse \
  $(ALL_EXAMPLE_DIRS_NO_KREMLIN)
else
ALL_EXAMPLE_DIRS=$(ALL_EXAMPLE_DIRS_NO_KREMLIN)
endif

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
