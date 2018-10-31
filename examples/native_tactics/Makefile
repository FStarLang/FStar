FSTAR_HOME=../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS)
FSTARTACLIB=$(FSTAR_HOME)/bin/fstar-tactics-lib/fstartaclib.cmxs

# Tests for which the native tactics used in module named Sample.Test.fst are
# declared in a corresponding module named Sample.fst
TAC_MODULES=Print\
    Split\
    BV\
    UnitTests\
    Bane\
    Canon\
    Simple\
    SimpleTactic\
    Evens\
    Embeddings\
    Plugins\
    Registers.List

# Tests for which the native tatics are declared and used in the same module
ALL=Apply\
    Arith\
    CanonDeep\
    Clear\
    Cut\
    DependentSynth\
    Fail\
    Imp\
    Logic\
    Nest\
    Pruning\
    Rename\
    Retype\
    Sequences\
    Simplifier\
    Tutorial\
    Unify

OTHERFLAGS += --use_extracted_interfaces false --use_two_phase_tc false

all: $(addsuffix .sep.test, $(TAC_MODULES)) $(addsuffix .test, $(ALL))

# .depend:
# 	$(FSTAR) --dep full $(addsuffix .Test.fst, $(ALL)) > .depend

# include .depend

.PHONY: %.test
.PRECIOUS: %.ml

%.test: %.fst %.ml
	$(FSTAR) $*.fst --load $*
	touch $@

%.sep.test: %.fst %.ml
	$(FSTAR) $*.Test.fst --load $*
	touch $@

%.ml: %.fst
	$(FSTAR) $*.fst --cache_checked_modules --codegen Plugin --extract $*
	touch $@

%.clean:
	rm -f Registers_List.ml Registers.List.ml Registers_List.cmxs

%.native: %.fst Registers.List.ml
	$(FSTAR) $*.fst --load Registers.List --warn_error -266

%.interp: %.fst Registers.List.fst
	$(FSTAR) $*.fst


clean:
	rm -f *.test *.ml *.o *.cm[ix] *.cmxs
