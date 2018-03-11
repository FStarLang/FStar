FSTAR_HOME=../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) --cache_checked_modules

ALL=Simple SimpleTactic

all: $(addsuffix .test, $(ALL))

.depend:
	$(FSTAR) --dep full $(addsuffix .Test.fst, $(ALL)) > .depend

include .depend

%.test: taclib %.ml
	$(FSTAR) $*.Test.fst --load $*

%.fst.checked:
	$(FSTAR) $<
	touch -ac $@

%.fsti.checked:
	$(FSTAR) $<
	touch -ac $@

%.ml: %.fst.checked
	$(FSTAR) $*.fst --codegen Plugin --extract $*

FSTARTACLIB=$(FSTAR_HOME)/bin/fstar-tactics-lib/fstartaclib.cmxs

taclib: $(FSTARTACLIB)

$(FSTARTACLIB):
	$(MAKE) -C $(FSTAR_HOME)/ulib install-fstar-tactics
