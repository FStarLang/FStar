include Makefile.include

all:
	# make -C bug-reports
	# make -C data_structures
	# make -C algorithms
	# make -C crypto
	# make -C security
	# make -C termination
	make -C software_foundations
	make -C metatheory
	make -C ../doc/tutorial/code/solutions
	make -C unit-tests

stdlib: $(addprefix ../lib/, list.fst string.fst partialmap.fst st.fst listproperties.fst)
	mkdir -p ../cache
	$(RUNTIME) ../bin/fstar.exe $(OTHERFLAGS) $^ --serialize_mods


clean:
	rm ../cache/*.cache
