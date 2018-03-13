FSTAR_HOME=../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS)
#--cache_checked_modules

ALL=Print Split BV UnitTests Canon Simple SimpleTactic Evens Embeddings

all: $(addsuffix .test, $(ALL))

# .depend:
# 	$(FSTAR) --dep full $(addsuffix .Test.fst, $(ALL)) > .depend

# include .depend

.PHONY: %.test fstartaclib

FSTARTACLIB=$(FSTAR_HOME)/bin/fstar-tactics-lib/fstartaclib.cmxs

$(FSTARTACLIB):
	$(MAKE) -C $(FSTAR_HOME)/ulib install-fstar-tactics

%.test: %.Test.fst %.ml
	$(FSTAR) $*.Test.fst --load $*
	touch $@

%.ml: %.fst $(FSTARTACLIB)
	$(FSTAR) $*.fst --codegen Plugin --extract $*
	touch $@

clean:
	rm -f *.test *.ml *.o *.cm[ix] *.cmxs
