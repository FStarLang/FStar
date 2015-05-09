VERFILES=unit1.fst unit2.fst testset.fst short-circuit.fst
include ../Makefile.include
NEGFILES=negative-tests.fst

all: .all.ver testmref all-neg

all-neg: $(NEGFILES)
	-$(FSTAR) --admit_fsi Set $(STDLIB) $^
	@echo "---------------------------------------"
	@echo "       Done ! EXPECT 32 FAILURES       "
	@echo "---------------------------------------"


inverse:
	$(FSTAR) --admit_fsi Seq $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst $(FSTAR_HOME)/lib/seq.fsi inverse.fst --max_fuel 0 --max_ifuel 3 --initial_ifuel 3 --initial_fuel 0

testmref:
	$(FSTAR) testmref.fst

test:

	$(FSTAR) --admit_fsi Seq $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst $(FSTAR_HOME)/lib/seq.fsi $(FSTAR_HOME)/lib/seqproperties.fst test.fst --admit_smt_queries true --max_fuel 0 --max_ifuel 0 --initial_ifuel 0 --initial_fuel 0
