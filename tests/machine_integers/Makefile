FSTAR_ROOT ?= ../..
FSTAR_FILES = $(wildcard Test*.fst)
include $(FSTAR_ROOT)/mk/test.mk

.PHONY: %.run clean
.PRECIOUS: %.exe %.out

all: $(patsubst %.fst,%.run,$(FSTAR_FILES)) BigList.memcheck

accept: $(patsubst %.fst,%.run-accept,$(FSTAR_FILES))

%.exe: %.fst
	$(call msg, "BUILD", $(notdir $@))
	$(eval B := $(patsubst %.exe,%,$@))
	$(Q)$(FSTAR) --odir out --codegen OCaml --extract '${B}' '${B}.fst'
	$(Q)/bin/echo -e '\n\nlet _ = main ()\n' >> out/${B}.ml
	$(Q)$(OCAMLOPT) -package fstar.lib -linkpkg out/${B}.ml -o $@

%.out: %.exe
	$(call msg, "OUTPUT", $(notdir $@))
	$(Q)./$< > $@

%.run: %.out
	$(Q)diff -u --strip-trailing-cr $<.expected $<

%.run-accept: %.out
	cp $< $<.expected

# Test that this file does not use much memory (currently 580MB),
# we give it 1.5GB
BigList.memcheck: BigList.fst
	$(call msg, "MEMCHECK", $<)
	( ulimit -v 1500000 && $(FSTAR) BigList.fst )
	touch $@
