include Makefile.include

all:
	make -C bug-reports
	make -C data_structures
	make -C algorithms
	make -C crypto
	make -C security
	make -C termination
	make -C software_foundations
	make -C metatheory
	make -C wf
	make -C wysteria
	make -C ../doc/tutorial/code/solutions
	make -C unit-tests
	make -C ../contrib/Platform/ml/
	make -C ../contrib/CoreCrypto/ml/

test: all

stdlib: $(addprefix ../lib/, list.fst string.fst partialmap.fst st.fst listproperties.fst)
	mkdir -p ../cache
	../bin/fstar.exe $(OTHERFLAGS) $^ --serialize_mods


clean:
	rm ../cache/*.cache

wc:
	find . -name "*.fst" | grep -v -e to_be_ported | xargs sloccount
