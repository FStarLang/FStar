# This makefile is old, and does not use the new test.mk infra. We could
# extend test.mk to be more aware of plugins and loading, but probably the right
# thing to do instead is to make using plugins easier at the F* level, without
# requiring any --load flags. In that case, this whole directory may just be a normal
# 'include test.mk'.

FSTAR_HOME=../..
OTHERFLAGS += --z3version 4.13.3
FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
MY_FSTAR_EXE=$(FSTAR_EXE) $(OTHERFLAGS)

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
    Registers.List\
    Sealed.Plugins \
		LocalState

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

all: $(addsuffix .sep.test, $(TAC_MODULES)) $(addsuffix .test, $(ALL))

# .depend:
# 	$(FSTAR_EXE) --dep full $(addsuffix .Test.fst, $(ALL)) --output_deps_to .depend

# include .depend

.PHONY: %.test
.PRECIOUS: %.ml

%.test: %.fst %.ml
	$(MY_FSTAR_EXE) $*.fst --load $*
	touch $@

%.sep.test: %.fst %.ml
	$(MY_FSTAR_EXE) $*.Test.fst --load $*
	touch $@

%.ml: %.fst
	$(MY_FSTAR_EXE) $*.fst --cache_checked_modules --codegen Plugin --extract $*
	touch $@

%.clean:
	rm -f Registers_List.ml Registers.List.ml Registers_List.cmxs

%.native: %.fst Registers.List.ml
	$(MY_FSTAR_EXE) $*.fst --load Registers.List --warn_error -266

%.interp: %.fst Registers.List.fst
	$(MY_FSTAR_EXE) $*.fst


clean:
	rm -f *.test *.ml *.o *.cm[ix] *.cmxs
