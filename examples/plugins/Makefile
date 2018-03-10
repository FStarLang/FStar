FSTAR?=fstar $(OTHERFLAGS) --cache_checked_modules

ALL=Plugin.Simple Plugin.Tactic

all: $(addsuffix .test, $(ALL))

.depend:
	$(FSTAR) --dep full $(addsuffix .Test.fst, $(ALL)) > .depend

include .depend

%.test: taclib %.fst.checked
	$(FSTAR) $*.fst --codegen Plugin --extract $*
	$(FSTAR) $*.Test.fst --load $*

test: taclib Plugin.Simple.fst.checked
	$(FSTAR) Plugin.Simple.fst --codegen Plugin --extract Plugin.Simple
	$(FSTAR) Plugin.Simple.Test.fst --load Plugin.Simple

%.fst.checked:
	$(FSTAR) $<
	touch -ac $@

%.fsti.checked:
	$(FSTAR) $<
	touch -ac $@

FSTARTACLIB=$(FSTAR_HOME)/bin/fstar-tactics-lib/fstartaclib.cmxs

taclib: $(FSTARTACLIB)

$(FSTARTACLIB):
	$(MAKE) -C $(FSTAR_HOME)/ulib install-fstar-tactics
