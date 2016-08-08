# These only verify under --stratified
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

all: sall uall

uall: uall-pos
	+make -C universes

sall: sall-pos sall-neg

uall-pos: FirstProofs.uver ShortCircuit.uver Unit1.Projectors1.uver Unit1.Projectors2.uver Unit1.UnificationTests.uver TestTwoLevelHeap.uver TestMRef.uver

sall-pos: Unit1.Basic.sver-nolib Unit1.WPsAndTriples.sver-nolib Unit1.RefinementInference.sver-nolib  Unit1.WPsAndTriples_ST.sver-nolib unit2.sver-nolib testghost.sver-nolib inverse.sver-nolib testset.sver-nolib testheap.sver-nolib Unit1.Parser.sver-nolib mac.sver-nolib

ubasictests: $(UVERFILES)
	$(FSTAR) $^

basictests: $(SVERFILES)
	$(SFSTAR) --explicit_deps $(STDLIB) $(call add_stdlib_prefix, FStar.Int32.fst) $^

sall-neg: $(NEGFILES)
	-$(SFSTAR) --explicit_deps $(STDLIB) --split_cases 1 $^ 2>&1 | tee fstar_log
	@FAILC=`egrep "^Error: [0-9]* errors" -o fstar_log | egrep -o "[0-9]+"`; if [ "$$FAILC" != "$(NEGTESTS)" ]; then echo "Wrong failure count: $$FAILC (expected $(NEGTESTS))" && false; else echo "Success: $$FAILC failures were expected"; fi

mac: mac.fst
	$(FSTAR)  mac.fst

inverse:
	$(FSTAR) --max_fuel 0 --max_ifuel 3 --initial_ifuel 3 --initial_fuel 0 $(call add_stdlib_prefix, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Seq.fst) inverse.fst

testghost:
	$(FSTAR) testghost.fst


