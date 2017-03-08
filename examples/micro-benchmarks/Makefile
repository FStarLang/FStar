VERFILES=
	 #inverse.fst

FSTAR_HOME=../..
include ../Makefile.include

NEGFILES=NegativeTests.BST.fst     NegativeTests.Heap.fst  NegativeTests.ShortCircuiting.fst \
	 NegativeTests.Bug260.fst  NegativeTests.Neg.fst   NegativeTests.Termination.fst \
	 NegativeTests.False.fst   NegativeTests.Set.fst   NegativeTests.ImplicitFalse.fst \
         NegativeTests.Positivity.fst


# if the `--lax` flag is used, negative tests will report a single error.
ifeq ($(filter $(OTHERFLAGS),--lax),)
NEGTESTS=40
else
NEGTESTS=3
endif

all: uall

uall: all-pos all-neg

all-pos: Unit1.Basic.uver Unit1.Projectors2.uver Unit1.WPsAndTriples.uver Unit1.Parser.uver \
	 Unit1.RefinementInference.uver Unit1.WPsAndTriples_ST.uver Unit1.Projectors1.uver \
	 Unit1.UnificationTests.uver Unit1.RecursiveTypeFunctions.uver \
	 Unit2.uver TestSet.uver TestHeap.uver ShortCircuit.uver FirstProofs.uver TestMRef.uver \
	 TestTwoLevelHeap.uver Mac.uver TestGhost.uver Normalization.uver Positivity.uver DoNotation.fst
	#TestHasEq.uver #temporarily removed from mac_universes branch

basictests: $(VERFILES)
	$(FSTAR) --explicit_deps $(STDLIB) $(call add_stdlib_prefix, FStar.Int32.fst) $^

all-neg: $(NEGFILES)
	-$(FSTAR) $^ 2>&1 | tee fstar_log
	@FAILC=`egrep "^[0-9]* errors were reported" -o fstar_log | egrep -o "[0-9]+"`; if [ "$$FAILC" != "$(NEGTESTS)" ]; then echo "Wrong failure count: $$FAILC (expected $(NEGTESTS))" && false; else echo "Success: $$FAILC failures were expected"; fi

mac2: mac2.fst
	$(FSTAR) --explicit_deps $(STDLIB) FStar.Seq.fst mac2.fst

inverse:
	$(FSTAR) --explicit_deps --max_fuel 0 --max_ifuel 3 --initial_ifuel 3 --initial_fuel 0 $(call add_stdlib_prefix, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Seq.fst) inverse.fst

testghost:
	$(FSTAR) testghost.fst


CFSTAR=$(subst CURRENT_DIR,examples/micro-benchmarks,$(CVERFSTAR))
all-cver: Unit1.Basic.ucver Unit1.Projectors2.ucver Unit1.WPsAndTriples.ucver Unit1.Parser.ucver \
	 Unit1.RefinementInference.ucver Unit1.WPsAndTriples_ST.ucver Unit1.Projectors1.ucver \
	 Unit1.UnificationTests.ucver Unit1.RecursiveTypeFunctions.ucver \
	 Unit2.ucver TestSet.ucver TestHeap.ucver ShortCircuit.ucver FirstProofs.ucver TestMRef.ucver \
	 TestTwoLevelHeap.ucver Mac.ucver TestGhost.ucver Normalization.ucver Positivity.ucver 
