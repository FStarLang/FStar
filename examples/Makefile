FSTAR_HOME=..
include Makefile.include

ALL_EXAMPLE_DIRS=\
bug-reports \
low-level \
data_structures \
algorithms \
crypto \
termination \
software_foundations \
../doc/tutorial/code/exercises \
../doc/tutorial/code/solutions \
rel \
maths \
paradoxes \
printf \
metatheory \
verifythis \
preorders \
dm4free \
incl \
micro-benchmarks

# #	make -C bignum  -- big timeout (30) + failing asserts (even with 50)
# #	make -C stateful_bignum  -- huge timeout (50) + code duplication (prims)
# #                                 + unfound identifiers in multiplication
# #	make -C extraction -- missing Makefile -- might move to unit-tests?
# # CH: how about moving the rest to an "experimental" dir/sub-dir?
# #	make -C circuitcompiler  -- doesn't seem ready for this yet
# #	make -C jsbackend -- no JavaScript backend yet
# #	make -C low-star -- doesn't build and needs OCaml, so maybe in make test
# #	make -C monads -- just an experiment, not fully working
# #	make -C test -- just an experiment, trying to optimize SMT encoding
# #	make -C deriving-monads -- still some failing assertions + missing Makefile

# WARNING: this target shouldn't depend on anything other than the F*
# binary; in particular it shouldn't depend on OCaml, F#, git, etc.
all: $(addsuffix .all, $(ALL_EXAMPLE_DIRS))

%.all: %
	+make -C $^ all

test: all

stdlib: $(addprefix ../lib/, FStar.List.fst FStar.String.fsti partialmap.fst FStar.ST.fst FStar.ListProperties.fst)
	mkdir -p ../cache
	$(FSTAR) $^ --serialize_mods

clean:
	rm ../cache/*.cache

wc:
	find . -name "*.fst" | grep -v -e to_be_ported | xargs sloccount
