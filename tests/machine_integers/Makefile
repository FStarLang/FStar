.PHONY: %.run clean
.PRECIOUS: %.exe %.out

FSTAR_HOME=../..

include $(FSTAR_HOME)/examples/Makefile.include
include $(FSTAR_HOME)/ulib/ml/Makefile.include

MODULES=$(wildcard Test*.fst)

all: $(patsubst %.fst,%.run,$(MODULES))

accept: $(patsubst %.fst,%.run-accept,$(MODULES))

%.exe: %.fst | out
	$(eval B := $(patsubst %.exe,%,$@))
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract '${B}' '${B}.fst'
	/bin/echo -e '\n\nlet _ = main ()\n' >> out/${B}.ml
	$(OCAMLOPT) out/${B}.ml -o $@

%.out: %.exe
	./$< > $@

%.run: %.out
	diff $<.expected $<

%.run-accept: %.out
	cp $< $<.expected

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *.exe
