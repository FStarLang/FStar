all: verify extract

ifneq (,$(FSTAR_HOME))
  FSTAR=$(FSTAR_HOME)/bin/fstar.exe
else
  FSTAR=fstar.exe
endif

INCLUDES=../../lib/steel/pulse ../../lib/steel
FSTAR_FILES:=$(wildcard *.fst *.fsti)
FSTAR_OPTIONS=$(OTHERFLAGS) --cache_checked_modules --warn_error @241 --already_cached '*,-PulseExtract' $(addprefix --include , $(INCLUDES))

include ../../lib/steel/runlim.mk

MY_FSTAR=$(RUNLIM) $(FSTAR) $(SIL) $(FSTAR_OPTIONS)

%.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	@# You can debug with --debug $(basename $(notdir $<))
	$(Q)$(RUNLIM) $(MY_FSTAR) $(SIL) $<
	touch -c $@

.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND")
	$(Q)true $(shell rm -f .depend.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(Q)$(MY_FSTAR) --dep full @$@.rsp > $@.tmp
	mv $@.tmp $@

include .depend

verify: $(ALL_CHECKED_FILES)

extract: verify
	$(MY_FSTAR) --codegen OCaml --odir ../ocaml/plugin/generated PulseExtract.Main.fst --extract PulseExtract.Main


clean:
	rm -f .depend* *.checked

.PHONY: all verify extract clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)
