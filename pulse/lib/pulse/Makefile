PULSE_HOME ?= $(realpath ../..)

all: core pulse ocaml lib c

.PHONY: ocaml
ocaml:
	cd ../../src/ocaml && dune build && dune install --prefix=$(PULSE_HOME)

.PHONY: core
core:
	+$(MAKE) -C $@

.PHONY: lib
lib: core pulse ocaml
	+$(MAKE) -C $@

.PHONY: c
c: lib
	+$(MAKE) -C $@

ifneq (,$(FSTAR_HOME))
  FSTAR=$(FSTAR_HOME)/bin/fstar.exe
else
  FSTAR=fstar.exe
endif

FSTAR_FILES:=$(wildcard *.fst *.fsti)

FSTAR_OPTIONS=$(OTHERFLAGS) --cache_checked_modules --warn_error @241 --already_cached '*,-Pulse,-PulseSyntaxExtension'

include runlim.mk

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

clean: clean-ocaml clean-fstar

.PHONY: clean-ocaml
clean-ocaml:
	cd ../../src/ocaml && { dune uninstall --prefix=$(PULSE_HOME) ; dune clean ; true ; }

.PHONY: clean-fstar
clean-fstar:
	find . -name '*.checked' -or -name '.depend*' | xargs rm -f

.PHONY: all pulse clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: install-pulse install
install: install-pulse

.PHONY: %.install %.install-dir

%.install: %
	$(INSTALL) -m 644 -D $< $(PREFIX)/lib/pulse/$<

%.install-dir: %
	find $< -type f -exec $(INSTALL) -m 644 -D '{}' $(PREFIX)/lib/pulse/'{}' ';'

install_subdirs=. core lib c
install_other_dirs=lib/class lib/ml lib/pledge

install: $(addsuffix .install,$(wildcard $(addsuffix /*.fst,$(install_subdirs)) $(addsuffix /*.fsti,$(install_subdirs)) $(addsuffix /*.checked,$(install_subdirs)))) $(addsuffix .install-dir,$(install_other_dirs)) install-ocaml

.PHONY: install-ocaml
install-ocaml:
	cd ../../src/ocaml && dune install --prefix=$(PREFIX)
