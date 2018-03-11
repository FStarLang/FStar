FSTAR_HOME=../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) --cache_checked_modules

ALL=Print Split BV UnitTests Canon

all: $(addsuffix .Test.fst.checked, $(ALL))

.depend:
	$(FSTAR) --dep full $(addsuffix .Test.fst, $(ALL)) > .depend

include .depend

%.test: %.Test.fst.checked

%.Test.fst.checked: $(FSTARTACLIB) %.ml
	$(FSTAR) $*.Test.fst --load $*
	touch -ac $@

%.fst.checked:
	$(FSTAR) $<
	touch -ac $@

%.fsti.checked:
	$(FSTAR) $<
	touch -ac $@

%.ml: %.fst.checked
	$(FSTAR) $*.fst --codegen Plugin --extract $*

FSTARTACLIB=$(FSTAR_HOME)/bin/fstar-tactics-lib/fstartaclib.cmxs

$(FSTARTACLIB):
	$(MAKE) -C $(FSTAR_HOME)/ulib install-fstar-tactics
