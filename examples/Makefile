include Makefile.include

# WARNING: this target shouldn't depend on anything other than the F*
# binary; in particular it shouldn't depend on OCaml, F#, git, etc.
all:
	make -C bug-reports
	make -C data_structures
	make -C algorithms
	make -C crypto
	make -C security
	make -C termination
	make -C software_foundations
	make -C ../doc/tutorial/code/solutions
	make -C relational
	make -C low-level
#	make -C low-star
	make -C maths
	make -C paradoxes
	make -C printf
	make -C verifythis
#	make -C bignum  -- big timeout (30) + failing asserts (even with 50)
#	make -C stateful_bignum  -- huge timeout (50) + code duplication (prims)
#                                 + unfound identifiers in multiplication
#	make -C extraction -- missing Makefile -- might move to unit-tests?
# CH: how about moving the rest to an "experimental" dir/sub-dir?
#	make -C circuitcompiler  -- doesn't seem ready for this yet
#	make -C jsbackend -- no JavaScript backend yet
#	make -C low-star -- doesn't build and needs OCaml, so maybe in make test
#	make -C monads -- just an experiment, not fully working
#	make -C test -- just an experiment, trying to optimize SMT encoding
#	make -C deriving-monads -- still some failing assertions + missing Makefile
	make -C metatheory
	make -C wysteria
	make -C unit-tests

test: all

stdlib: $(addprefix ../lib/, list.fst string.fst partialmap.fst st.fst listproperties.fst)
	mkdir -p ../cache
	../bin/fstar.exe $(OTHERFLAGS) $^ --serialize_mods


clean:
	rm ../cache/*.cache

wc:
	find . -name "*.fst" | grep -v -e to_be_ported | xargs sloccount
