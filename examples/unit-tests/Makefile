VERFILES=unit1.fst unit2.fst testset.fst short-circuit.fst
include ../Makefile.include
NEGFILES=negative-tests.fst

all: basictests testmref testhyperheap.vv mac2 all-neg

basictests: $(VERFILES)
		$(FSTAR) --admit_fsi Set $(STDLIB) $(FSTAR_HOME)/lib/int32.fst $^

all-neg: $(NEGFILES)
	-$(FSTAR) --admit_fsi Set $(STDLIB) --split_cases 1 $^
	@echo "---------------------------------------"
	@echo "       Done ! EXPECT 31 FAILURES       "
	@echo "---------------------------------------"


inverse:
	$(FSTAR) --admit_fsi Seq $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst $(FSTAR_HOME)/lib/seq.fsi inverse.fst --max_fuel 0 --max_ifuel 3 --initial_ifuel 3 --initial_fuel 0

testmref:
	$(FSTAR) --admit_fsi Set --logQueries --verify_module TestMRef --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1 $(FSTAR_HOME)/lib/ext.fst $(FSTAR_HOME)/lib/set.fsi $(FSTAR_HOME)/lib/heap.fst $(FSTAR_HOME)/lib/st.fst $(FSTAR_HOME)/lib/mref.fst testmref.fst

test:
	$(FSTAR) --admit_fsi Seq $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst $(FSTAR_HOME)/lib/seq.fsi $(FSTAR_HOME)/lib/seqproperties.fst test.fst --admit_smt_queries true --max_fuel 0 --max_ifuel 0 --initial_ifuel 0 --initial_fuel 0

mac2:
	$(FSTAR) $(FSTAR_HOME)/lib/ext.fst $(FSTAR_HOME)/lib/array.fst $(FSTAR_HOME)/lib/set.fsi $(FSTAR_HOME)/lib/set.fst $(FSTAR_HOME)/lib/heap.fst $(FSTAR_HOME)/lib/st.fst $(FSTAR_HOME)/lib/list.fst mac2.fst
