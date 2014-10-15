# -*- Makefile -*-

# --------------------------------------------------------------------
OCAMLBUILD_BIN   = ocamlbuild -use-ocamlfind
OCAMLBUILD_EXTRA = -classic-display

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_EXTRA += -classic-display
endif
OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_EXTRA)

AOUT = FSLangTest

# --------------------------------------------------------------------
.PHONY: all build byte native clean

all: build
	@true

build: native

define do-build
	$(OCAMLBUILD) "src/$(1)"
endef

byte:
	$(call do-build,$(AOUT).byte)

native:
	$(call do-build,$(AOUT).native)

clean:
	$(OCAMLBUILD) -clean
	rm -f $(AOUT).native* $(AOUT).byte*
