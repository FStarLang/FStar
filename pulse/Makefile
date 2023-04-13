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

.PHONY: verify
verify: verify-steel

clean:
	+$(MAKE) -C lib/steel clean ; true
	cd src/ocaml && { dune uninstall --prefix=$(STEEL_HOME) ; dune clean ; true ; }

.PHONY: test
test: all
	+$(MAKE) -C share/steel
