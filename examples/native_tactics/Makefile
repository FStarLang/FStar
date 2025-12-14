# This makefile is old, and does not use the new test.mk infra. We could
# extend test.mk to be more aware of plugins and loading, but probably the right
# thing to do instead is to make using plugins easier at the F* level, without
# requiring any --load flags. In that case, this whole directory may just be a normal
# 'include test.mk'.

FSTAR_HOME=../..
OTHERFLAGS += --ext optimize_let_vc --ext fly_deps
FSTAR_EXE ?= $(FSTAR_HOME)/out/bin/fstar.exe
FSTAR=$(FSTAR_EXE) $(OTHERFLAGS)

# Tests for which the native tactics used in module named Sample.Test.fst are
# declared in a corresponding module named Sample.fst
TAC_MODULES=Print\
    Split\
    BV\
    UnitTests\
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
# 	$(FSTAR) --dep full $(addsuffix .Test.fst, $(ALL)) -o $@

# include .depend

.PHONY: %.test
.PRECIOUS: %.ml

%.test: %.fst %.ml
	$(FSTAR) $*.fst --load $*
	touch -c $@

%.sep.test: %.fst %.ml
	$(FSTAR) $*.Test.fst --load $*
	touch -c $@

%.ml: %.fst
	$(FSTAR) $*.fst --cache_checked_modules --codegen Plugin --extract $*
	touch -c $@

%.clean:
	rm -f Registers_List.ml Registers.List.ml Registers_List.cmxs

%.native: %.fst Registers.List.ml
	$(FSTAR) $*.fst --load Registers.List --warn_error -266

%.interp: %.fst Registers.List.fst
	$(FSTAR) $*.fst

clean:
	rm -f *.test *.ml *.o *.cm[ix] *.cmxs
