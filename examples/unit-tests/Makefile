VERFILES=unit1.fst unit2.fst testset.fst short-circuit.fst
include ../Makefile.include
NEGFILES=negative-tests.fst
NEGTESTS=35

all: basictests testint32.vv testmref testhyperheap.vv mac2 all-neg

basictests: $(VERFILES)
		$(FSTAR) --admit_fsi Set $(STDLIB) $(FSTAR_HOME)/lib/int32.fst $^

all-neg: $(NEGFILES)
	-$(FSTAR) --admit_fsi Set $(STDLIB) --split_cases 1 $^ | tee fstar_log
	@FAILC=`egrep "^Error: [0-9]* errors" -o fstar_log | egrep -o "[0-9]*"`; if [ "$$FAILC" != "$(NEGTESTS)" ]; then echo "Wrong failure count: $$FAILC (expected $(NEGTESTS))" && false; else echo "Success: $$FAILC failures were expected"; fi


inverse:
	$(FSTAR) --admit_fsi Seq $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst $(FSTAR_HOME)/lib/seq.fsi inverse.fst --max_fuel 0 --max_ifuel 3 --initial_ifuel 3 --initial_fuel 0

testmref:
	$(FSTAR) testmref.fst
	
test:
	$(FSTAR) --admit_fsi Seq $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst $(FSTAR_HOME)/lib/seq.fsi $(FSTAR_HOME)/lib/seqproperties.fst test.fst --admit_smt_queries true --max_fuel 0 --max_ifuel 0 --initial_ifuel 0 --initial_fuel 0

mac2:
	$(FSTAR) $(FSTAR_HOME)/lib/ext.fst $(FSTAR_HOME)/lib/array.fst $(FSTAR_HOME)/lib/set.fsi $(FSTAR_HOME)/lib/set.fst $(FSTAR_HOME)/lib/heap.fst $(FSTAR_HOME)/lib/st.fst $(FSTAR_HOME)/lib/list.fst mac2.fst
