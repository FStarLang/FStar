all: steel pulse steelc

ifneq (,$(FSTAR_HOME))
  FSTAR=$(FSTAR_HOME)/bin/fstar.exe
else
  FSTAR=fstar.exe
endif

FSTAR_FILES:=$(wildcard *.fst *.fsti)

FSTAR_OPTIONS=$(OTHERFLAGS) --cache_checked_modules --warn_error @241 --already_cached '*,-Steel' --load_cmxs steel

COMPAT_INDEXED_EFFECTS=--compat_pre_typed_indexed_effects
MY_FSTAR=$(RUNLIM) $(FSTAR) $(SIL) $(FSTAR_OPTIONS)

%.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	@# You can debug with --debug $(basename $(notdir $<))
	$(Q)$(RUNLIM) $(MY_FSTAR) $(SIL) $(COMPAT_INDEXED_EFFECTS) $<
	touch -c $@

# These modules already verify without the flag.
Steel.ST.GhostPCMReference.fst.checked: COMPAT_INDEXED_EFFECTS=

.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND")
	$(Q)true $(shell rm -f .depend.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(Q)$(MY_FSTAR) --dep full @$@.rsp > $@.tmp
	mv $@.tmp $@

include .depend

steel: $(ALL_CHECKED_FILES)

.PHONY: pulse
pulse: steel
	+$(MAKE) -C $@

.PHONY: steelc
steelc: steel
	+$(MAKE) -C $@

clean:
	rm -f .depend* *.checked

.PHONY: all steel clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: install-steel install-pulse install-steelc install
install: install-steel install-pulse install-steelc

install-pulse:
	+$(MAKE) -C pulse install

install-steelc:
	+$(MAKE) -C c install

.PHONY: %.install

%.install: %
	$(INSTALL) -m 644 -D $< $(STEEL_INSTALL_PREFIX)/lib/steel/$<

install-steel: $(addsuffix .install,$(wildcard *.fst *.fsti *.checked) libsteel.a)
