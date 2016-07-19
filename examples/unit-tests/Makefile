# These only verify under --stratified
SVERFILES=Unit1.Basic.fst                  Unit1.WPsAndTriples.fst \
	     Unit1.RefinementInference.fst  Unit1.WPsAndTriples_ST.fst \
	     unit2.fst \
	     testghost.fst \
	     inverse.fst \
             testset.fst\
             testheap.fst\
             Unit1.Parser.fst\
             mac.fst
# These are ok under universes
UVERFILES= \
	FirstProofs.fst ShortCircuit.fst  \
 	Unit1.Projectors1.fst Unit1.Projectors2.fst Unit1.UnificationTests.fst  \
	testTwoLevelHeap.fst testmref.fst
	     		       
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

all: uall-pos all-pos all-neg
	+make -C universes



uall-pos:
	$(FSTAR) $(UVERFILES)

all-pos: 
	$(SFSTAR) $(SVERFILES)

ubasictests: $(UVERFILES)
	$(FSTAR) $^

basictests: $(SVERFILES)
	$(SFSTAR) --explicit_deps $(STDLIB) $(call add_stdlib_prefix, FStar.Int32.fst) $^

all-neg: $(NEGFILES)
	-$(SFSTAR) --explicit_deps $(STDLIB) --split_cases 1 $^ 2>&1 | tee fstar_log
	@FAILC=`egrep "^Error: [0-9]* errors" -o fstar_log | egrep -o "[0-9]+"`; if [ "$$FAILC" != "$(NEGTESTS)" ]; then echo "Wrong failure count: $$FAILC (expected $(NEGTESTS))" && false; else echo "Success: $$FAILC failures were expected"; fi

mac: mac.fst
	$(FSTAR)  mac.fst

inverse:
	$(FSTAR) --max_fuel 0 --max_ifuel 3 --initial_ifuel 3 --initial_fuel 0 $(call add_stdlib_prefix, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Seq.fst) inverse.fst

testghost:
	$(FSTAR) testghost.fst


