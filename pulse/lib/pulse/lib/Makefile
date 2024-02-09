PULSE_HOME ?= ../../..

all: pulse

ifneq (,$(FSTAR_HOME))
  FSTAR=$(FSTAR_HOME)/bin/fstar.exe
else
  FSTAR=fstar.exe
endif

# FIXME: do we still need such separate subdirectories?
SUBDIRS=\
	class \
	pledge \


INCLUDE_PATHS= \
	$(PULSE_HOME)/lib/pulse \
	$(PULSE_HOME)/lib/pulse/core \
	$(SUBDIRS)

FSTAR_FILES:=$(wildcard *.fst *.fsti $(addsuffix /*.fst,$(SUBDIRS)) $(addsuffix /*.fsti,$(SUBDIRS)))

FSTAR_OPTIONS=$(OTHERFLAGS) --cache_checked_modules --warn_error @241 --already_cached '*,-Pulse.Lib,-Pulse.Class' $(addprefix --include ,$(INCLUDE_PATHS)) --load_cmxs pulse

include $(PULSE_HOME)/lib/pulse/runlim.mk

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
