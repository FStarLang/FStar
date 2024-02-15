PULSE_HOME ?= $(realpath ../..)

all: verify

SRC_DIRS := . core lib lib/class lib/pledge c
FSTAR_OPTIONS += --already_cached '*,-Pulse,-PulseCore' --load_cmxs pulse

include $(PULSE_HOME)/share/pulse/Makefile.include-base

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

.PHONY: main
main: Pulse.Main.fsti.checked
