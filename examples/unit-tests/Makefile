VERFILES=unit1.fst unit2.fst testset.fst short-circuit.fst first-proofs.fst
include ../Makefile.include
NEGFILES=negative-tests.fst

# if the `--lax` flag is used, negative tests will report a single error.
ifeq ($(filter $(OTHERFLAGS),--lax),)
NEGTESTS=35
else
NEGTESTS=1
endif

all: all-pos all-neg

all-pos: basictests testint32.vv testmref.vv testTwoLevelHeap.vv mac2.vv testghost inverse testghost

basictests: $(VERFILES)
	$(FSTAR_OR_NUBUILD) --admit_fsi FStar.Set $(STDLIB) $(call add_stdlib_prefix, FStar.Int32.fst) $^

all-neg: $(NEGFILES)
	-$(FSTAR_OR_NUBUILD) --admit_fsi FStar.Set $(STDLIB) --split_cases 1 $^ | tee fstar_log
	@FAILC=`egrep "^Error: [0-9]* errors" -o fstar_log | egrep -o "[0-9]+"`; if [ "$$FAILC" != "$(NEGTESTS)" ]; then echo "Wrong failure count: $$FAILC (expected $(NEGTESTS))" && false; else echo "Success: $$FAILC failures were expected"; fi

inverse:
	$(FSTAR_OR_NUBUILD) --max_fuel 0 --max_ifuel 3 --initial_ifuel 3 --initial_fuel 0 --admit_fsi FStar.Seq $(call add_stdlib_prefix, FStar.Classical.fst FStar.FunctionalExtensionality.fst seq.fsi) inverse.fst

testghost:
	$(FSTAR_OR_NUBUILD) testghost.fst
