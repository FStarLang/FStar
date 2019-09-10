.PHONY: %.run clean
.PRECIOUS: %.exe

FSTAR_HOME=../..

include $(FSTAR_HOME)/examples/Makefile.include
include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: Test01.run Test02.run Test03.run

%.exe: %.fst | out
	$(eval B := $(patsubst %.exe,%,$@))
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract '${B}' '${B}.fst'
	echo '\n\nlet _ = main ()\n' >> out/${B}.ml
	$(OCAMLOPT) out/${B}.ml -o $@

%.run: %.exe
	./$< | grep correct

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *.exe
