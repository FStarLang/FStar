all: pulse

ifneq (,$(FSTAR_HOME))
  FSTAR=$(FSTAR_HOME)/bin/fstar.exe
else
  FSTAR=fstar.exe
endif

FSTAR_FILES:=$(wildcard *.fst *.fsti)

FSTAR_OPTIONS=$(OTHERFLAGS) --cache_checked_modules --warn_error @241 --already_cached '*,-Pulse' --include .. --load_cmxs steel

MY_FSTAR=$(RUNLIM) $(FSTAR) $(SIL) $(FSTAR_OPTIONS)

%.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	@# You can debug with --debug $(basename $(notdir $<))
	$(Q)$(RUNLIM) $(MY_FSTAR) $(SIL) $(COMPAT_INDEXED_EFFECTS) $<
	touch -c $@

.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND")
	$(Q)true $(shell rm -f .depend.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(Q)$(MY_FSTAR) --dep full @$@.rsp > $@.tmp
	mv $@.tmp $@

include .depend

pulse: $(ALL_CHECKED_FILES)

clean:
	rm -f .depend* *.checked

.PHONY: all pulse clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: install-pulse install
install: install-pulse

.PHONY: %.install

%.install: %
	$(INSTALL) -m 644 -D $< $(STEEL_INSTALL_PREFIX)/lib/steel/pulse/$<

install-pulse: $(addsuffix .install,$(wildcard *.fst *.fsti *.checked))
