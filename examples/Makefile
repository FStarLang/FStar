FSTAR_HOME=..
include Makefile.include

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
all: uall sall

uall:
	+make -C bug-reports uall
	+make -C data_structures uall
	+make -C algorithms uall
	+make -C crypto uall
	+make -C security uall
	+make -C termination uall
	+make -C software_foundations uall
	+make -C ../doc/tutorial/code/solutions uall
	+make -C relational uall
	+make -C voting uall
	+make -C low-level uall
	+make -C maths uall
	+make -C paradoxes uall
	+make -C printf uall
	+make -C verifythis uall
	+make -C metatheory uall
	+make -C wysteria uall
	+make -C preorders uall
	+make -C dm4free uall
	+make -C unit-tests uall

sall:
	+make -C bug-reports sall
	+make -C data_structures sall
	+make -C algorithms sall
	+make -C crypto sall
	+make -C security sall
	+make -C termination sall
	+make -C software_foundations sall
	+make -C ../doc/tutorial/code/solutions sall
	+make -C relational sall
	+make -C voting sall
	+make -C low-level sall
	+make -C maths sall
	+make -C paradoxes sall
	+make -C printf sall
	+make -C verifythis sall
	+make -C metatheory sall
	+make -C wysteria sall
	+make -C preorders sall
	+make -C dm4free sall
	+make -C unit-tests sall

test: all

stdlib: $(addprefix ../lib/, FStar.List.fst FStar.String.fsti partialmap.fst FStar.ST.fst FStar.ListProperties.fst)
	mkdir -p ../cache
	$(FSTAR) $^ --serialize_mods


clean:
	rm ../cache/*.cache

wc:
	find . -name "*.fst" | grep -v -e to_be_ported | xargs sloccount
