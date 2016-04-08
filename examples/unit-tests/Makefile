VERFILES=Unit1.Basic.fst        Unit1.Projectors2.fst          Unit1.WPsAndTriples.fst \
	 Unit1.Parser.fst       Unit1.RefinementInference.fst  Unit1.WPsAndTriples_ST.fst \
	 Unit1.Projectors1.fst  Unit1.UnificationTests.fst     unit2.fst \
	 testset.fst 		testheap.fst 		       short-circuit.fst \
	 first-proofs.fst 	              	 	       testmref.fst \
	 testTwoLevelHeap.fst   mac2.fst 		       testghost.fst \
	 inverse.fst

FSTAR_HOME=../..
include ../Makefile.include

NEGFILES=NegativeTests.BST.fst     NegativeTests.Heap.fst  NegativeTests.ShortCircuiting.fst \
	 NegativeTests.Bug260.fst  NegativeTests.Neg.fst   NegativeTests.Termination.fst \
	 NegativeTests.False.fst   NegativeTests.Set.fst


# if the `--lax` flag is used, negative tests will report a single error.
ifeq ($(filter $(OTHERFLAGS),--lax),)
NEGTESTS=36
else
NEGTESTS=1
endif

all: all-pos all-neg

all-pos: 
	$(FSTAR) $(VERFILES)

basictests: $(VERFILES)
	$(FSTAR) --explicit_deps $(STDLIB) $(call add_stdlib_prefix, FStar.Int32.fst) $^

all-neg: $(NEGFILES)
	-$(FSTAR) --explicit_deps $(STDLIB) --split_cases 1 $^ 2>&1 | tee fstar_log
	@FAILC=`egrep "^Error: [0-9]* errors" -o fstar_log | egrep -o "[0-9]+"`; if [ "$$FAILC" != "$(NEGTESTS)" ]; then echo "Wrong failure count: $$FAILC (expected $(NEGTESTS))" && false; else echo "Success: $$FAILC failures were expected"; fi

mac2: mac2.fst
	$(FSTAR) --explicit_deps $(STDLIB) FStar.Seq.fst mac2.fst

inverse:
	$(FSTAR) --explicit_deps --max_fuel 0 --max_ifuel 3 --initial_ifuel 3 --initial_fuel 0 $(call add_stdlib_prefix, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Seq.fst) inverse.fst

testghost:
	$(FSTAR) testghost.fst


