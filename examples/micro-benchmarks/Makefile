VERFILES=
	 #inverse.fst

FSTAR_HOME=../..
include ../Makefile.include



# if the `--lax` flag is used, negative tests will report a single error.
ifeq ($(filter $(OTHERFLAGS),--lax),)
NEGTESTS=41
else
NEGTESTS=3
endif

all: uall

uall: all-pos

all-pos: Unit1.Basic.uver Unit1.Projectors2.uver Unit1.WPsAndTriples.uver Unit1.Parser.uver \
	 Unit1.RefinementInference.uver Unit1.WPsAndTriples_ST.uver Unit1.Projectors1.uver \
	 Unit1.UnificationTests.uver Unit1.RecursiveTypeFunctions.uver  \
	 Unit2.uver TestSet.uver TestHeap.uver ShortCircuit.uver FirstProofs.uver TestMRef.uver \
	 TestTwoLevelHeap.uver Mac.uver TestGhost.uver Normalization.uver Positivity.uver DoNotation.uver \
	 Pruning.uver NormVsSMT.uver Unit1.TopLevelPats.uver AssumeRequires.uver TwoPhaseTC.uver \
	 IntNormalization.uver Subtyping.uver Test.HyperStack.uver Raising.uver RangeStep.uver \
	 WPExtensionality.uver UnifyMatch.uver UnifyRefs.uver \
	 NegativeTests.BST.uver     NegativeTests.Heap.uver  NegativeTests.ShortCircuiting.uver \
	 NegativeTests.Bug260.uver  NegativeTests.Neg.uver   NegativeTests.Termination.uver \
	 NegativeTests.False.uver   NegativeTests.Set.uver   NegativeTests.Positivity.uver \
	 NegativeTests.ZZImplicitFalse.uver StableErr.uver   ChrisCheck.uver PatCoerce.uver \
	 OccursCheckOnArrows.uver Test.Integers.uver AnotType.uver Test.ReifyNBE.fst TestHasEq.uver \
	 PatAnnot.uver

basictests: $(VERFILES)
	$(FSTAR) --explicit_deps $(STDLIB) $(call add_stdlib_prefix, FStar.Int32.fst) $^

mac2: mac2.fst
	$(FSTAR) --explicit_deps $(STDLIB) FStar.Seq.fst mac2.fst

inverse:
	$(FSTAR) --explicit_deps --max_fuel 0 --max_ifuel 3 --initial_ifuel 3 --initial_fuel 0 $(call add_stdlib_prefix, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Seq.fst) inverse.fst

testghost:
	$(FSTAR) testghost.fst
