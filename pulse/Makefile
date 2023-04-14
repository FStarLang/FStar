all: lib verify

ifneq (,$(FSTAR_HOME))
  ifeq ($(OS),Windows_NT)
    OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
  else
    OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
  endif
  export OCAMLPATH
endif

ifeq ($(OS),Windows_NT)
  STEEL_HOME := $(shell cygpath -m $(CURDIR))
else
  STEEL_HOME := $(CURDIR)
endif

.PHONY: ocaml
ocaml:
	cd src/ocaml && dune build
	cd src/ocaml && dune install --prefix=$(STEEL_HOME)

.PHONY: lib
lib:
	+$(MAKE) -C src/c

.PHONY: verify-steel
verify-steel: ocaml
	+$(MAKE) -C lib/steel steel

.PHONY: verify-pulse
verify-pulse: verify-steel
	+$(MAKE) -C lib/steel/pulse pulse

.PHONY: verify-steelc
verify-steelc: verify-steel
	+$(MAKE) -C lib/steel/c steelc

.PHONY: verify
verify: verify-steel verify-pulse verify-steelc

clean:
	+$(MAKE) -C lib/steel clean ; true
	cd src/ocaml && { dune uninstall --prefix=$(STEEL_HOME) ; dune clean ; true ; }

.PHONY: test
test: all
	+$(MAKE) -C share/steel

ifeq ($(OS),Windows_NT)
  STEEL_INSTALL_PREFIX=$(shell cygpath -m $(PREFIX))
else
  STEEL_INSTALL_PREFIX=$(PREFIX)
endif
export STEEL_INSTALL_PREFIX

INSTALL := $(shell ginstall --version 2>/dev/null | cut -c -8 | head -n 1)
ifdef INSTALL
   INSTALL := ginstall
else
   INSTALL := install
endif
export INSTALL

.PHONY: install install-ocaml install-lib install-include install-share

install-ocaml:
	cd src/ocaml && dune install --prefix=$(STEEL_INSTALL_PREFIX)

install-lib:
	+$(MAKE) -C lib/steel install

install-include:
	+$(MAKE) -C include/steel install

install-share:
	+$(MAKE) -C share/steel install

install: install-ocaml install-lib install-include install-share
