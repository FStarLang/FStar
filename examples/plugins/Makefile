FSTAR?=fstar $(OTHERFLAGS) --cache_checked_modules

all: test

.depend:
	$(FSTAR) --dep full Plugin.Simple.Test.fst > .depend

include .depend

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
