FSTAR = ../../../bin/fstar.exe
LIB=../../../lib/

RO_OTHER_FILES=$(addprefix $(LIB), set.fsi heap.fst st.fst all.fst st2.fst bytes.fst list.fst) ../sample.fst ../xor.fst ../ro.fst
SPDZ_OTHER_FILES=$(addprefix $(LIB), set.fsi heap.fst st.fst all.fst st2.fst) ../sample.fst ../spdz.fst 

all:clean\
		test_all\
		ro_all\
		spdz_all

clean:
	rm *_projected.fst; true


test_all:test\
				 test_projections

test:
	$(FSTAR) test.fst

test_projections:
	$(FSTAR) TEST_projected.fst
	$(FSTAR) TEST2_projected.fst
	$(FSTAR) TEST3_projected.fst

ro_all:ro\
			 ro_projections

ro:
	$(FSTAR) ro.fst

ro_projections:
	$(FSTAR) --verify_module RoTest --admit_fsi FStar.Set $(RO_OTHER_FILES) RoTest_projected.fst
	$(FSTAR) --verify_module RoTest2 --admit_fsi FStar.Set $(RO_OTHER_FILES) RoTest2_projected.fst

spdz_all: spdz\
					spdz_projections

spdz:
	$(FSTAR) spdz.fst

spdz_projections:
	$(FSTAR) --verify_module SpdzTest  --admit_fsi FStar.Set $(SPDZ_OTHER_FILES) SpdzTest_projected.fst
