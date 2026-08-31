# This makefile is old, and does not use the new test.mk infra. We could
# extend test.mk to be more aware of plugins and loading, but probably the right
# thing to do instead is to make using plugins easier at the F* level, without
# requiring any --load flags. In that case, this whole directory may just be a normal
# 'include test.mk'.

FSTAR_HOME=../..
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

.PRECIOUS: %.ml

# Every stamp and cache below must depend on the compiler: a .checked file is
# keyed only on its source, so without this a stamp left by an older binary
# satisfies make and the test silently never runs again.  (An OOM regression in
# Registers.List.Test hid this way through a full local `make test`.)

%.test: %.fst %.ml $(FSTAR_EXE)
	$(FSTAR) $*.fst --load $*
	touch $@

# Note the dependency on the .Test.fst: that, not %.fst, is what is checked here.
%.sep.test: %.fst %.Test.fst %.ml $(FSTAR_EXE)
	$(FSTAR) $*.Test.fst --load $*
	touch $@

%.fst.checked: %.fst $(FSTAR_EXE)
	$(FSTAR) $< --cache_checked_modules
	touch -c $@

# Extract step must not use fly_deps: it skips cache for CLI files,
# which conflicts with CMI requiring modules to be pre-checked.
%.ml: %.fst.checked $(FSTAR_EXE)
	$(FSTAR_EXE) --ext optimize_let_vc $*.fst --cache_checked_modules --codegen Plugin --extract $*
	touch -c $@

%.clean:
	rm -f Registers_List.ml Registers.List.ml Registers_List.cmxs

%.native: %.fst Registers.List.ml
	$(FSTAR) $*.fst --load Registers.List --warn_error -266

%.interp: %.fst Registers.List.fst
	$(FSTAR) $*.fst

clean:
	rm -f *.test *.ml *.o *.cm[ix] *.cmxs *.checked
