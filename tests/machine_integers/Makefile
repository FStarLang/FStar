.PHONY: %.run clean
.PRECIOUS: %.exe %.out

FSTAR_HOME=../..

include $(FSTAR_HOME)/examples/Makefile.include
include $(FSTAR_HOME)/ulib/ml/Makefile.include

MODULES=$(wildcard Test*.fst)

all: $(patsubst %.fst,%.run,$(MODULES)) out/BigList.memcheck

accept: $(patsubst %.fst,%.run-accept,$(MODULES))

%.exe: %.fst | out
	$(call msg, "BUILD", $(notdir $@))
	$(eval B := $(patsubst %.exe,%,$@))
	rm -f "out/${B}.ml"
	$(Q)$(FSTAR) $(SIL) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract '${B}' '${B}.fst'
	$(Q)/bin/echo -e '\n\nlet _ = main ()\n' >> out/${B}.ml
	$(Q)$(OCAMLOPT) out/${B}.ml -o $@

%.out: %.exe
	$(call msg, "OUTPUT", $(notdir $@))
	$(Q)./$< > $@

%.run: %.out
	$(Q)diff -u --strip-trailing-cr $<.expected $<

%.run-accept: %.out
	cp $< $<.expected

out:
	mkdir -p out

# Test that this file does not use much memory (currently 580MB),
# we give it 1.5GB
out/BigList.memcheck: BigList.fst
	$(call msg, "MEMCHECK", $<)
	$(Q)( ulimit -v 1500000 && $(FSTAR) $(SIL) BigList.fst )
	$(Q)touch $@

clean:
	rm -rf out
	rm -f *.exe
