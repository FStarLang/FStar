# Pulse's `Makefile`s rely on recent GNU Make's "shortest stem" rule,
# so we need to rule out older `make`s.

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

all: build

# Find fstar.exe and the fstar.lib OCaml package
ifeq (,$(FSTAR_HOME))
  _check_fstar := $(shell which fstar.exe)
  ifeq ($(.SHELLSTATUS),0)
    _fstar_home := $(realpath $(dir $(_check_fstar))/..)
    ifeq ($(OS),Windows_NT)
      OCAMLPATH := $(shell cygpath -m $(_fstar_home)/lib);$(OCAMLPATH)
    else
      OCAMLPATH := $(_fstar_home)/lib:$(OCAMLPATH)
    endif
  endif
else
  _fstar_home := $(FSTAR_HOME)
  ifeq ($(OS),Windows_NT)
    OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
  else
    OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
  endif
endif
export OCAMLPATH
_check_fstar_lib_package := $(shell env OCAMLPATH="$(OCAMLPATH)" ocamlfind query fstar.lib)
ifneq ($(.SHELLSTATUS),0)
  $(error "Cannot find fstar.lib in $(OCAMLPATH). Please make sure fstar.exe is properly installed and in your PATH or FSTAR_HOME points to its prefix directory or the F* source repository.")
endif

# Define the Pulse root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
ifeq ($(OS),Windows_NT)
  PULSE_HOME := $(shell cygpath -m $(CURDIR))
else
  PULSE_HOME := $(CURDIR)
endif

.PHONY: build
build:
	+$(MAKE) -C lib/pulse

clean:
	+$(MAKE) -C lib/pulse clean ; true

.PHONY: test
test: all
	+$(MAKE) -C share/pulse

ifeq (,$(PREFIX))
  PREFIX := /usr/local
endif
ifeq ($(OS),Windows_NT)
  PREFIX := $(shell cygpath -m $(PREFIX))
endif
export PREFIX

INSTALL := $(shell ginstall --version 2>/dev/null | cut -c -8 | head -n 1)
ifdef INSTALL
   INSTALL := ginstall
else
   INSTALL := install
endif
export INSTALL

.PHONY: install install-lib install-share

install-lib:
	+$(MAKE) -C lib/pulse install

install-share:
	+$(MAKE) -C share/pulse install

install: install-lib install-share

.PHONY: pulse2rust
pulse2rust:
	+$(MAKE) -C pulse2rust

.PHONY: boot
boot:
	+$(MAKE) -C src boot

.PHONY: ci
ci:
	+$(MAKE) -C src ci
