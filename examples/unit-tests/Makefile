VERFILES=unit1.fst unit2.fst testset.fst short-circuit.fst first-proofs.fst
include ../Makefile.include
NEGFILES=negative-tests.fst
NEGTESTS=35

all: all-pos all-neg

all-pos: basictests testint32.vv testmref.vv testTwoLevelHeap.vv mac2.vv testghost inverse testghost

basictests: $(VERFILES)
		$(FSTAR) --admit_fsi FStar.Set $(STDLIB) FStar.Int32.fst $^

all-neg: $(NEGFILES)
	-$(FSTAR) --admit_fsi FStar.Set $(STDLIB) --split_cases 1 $^ | tee fstar_log
	@FAILC=`egrep "^Error: [0-9]* errors" -o fstar_log | egrep -o "[0-9]+"`; if [ "$$FAILC" != "$(NEGTESTS)" ]; then echo "Wrong failure count: $$FAILC (expected $(NEGTESTS))" && false; else echo "Success: $$FAILC failures were expected"; fi


inverse:
	$(FSTAR) --admit_fsi FStar.Seq FStar.Classical.fst FStar.FunctionalExtensionality.fst seq.fsi inverse.fst --max_fuel 0 --max_ifuel 3 --initial_ifuel 3 --initial_fuel 0

testghost:
	$(FSTAR) testghost.fst
