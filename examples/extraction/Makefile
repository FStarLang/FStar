FSTAR_HOME=../..
include ../Makefile.include
include $(FSTAR_HOME)/ulib/ml/Makefile.include

eta_expand: out Eta_expand.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Eta_expand.fst
	$(OCAMLOPT) out/Eta_expand.ml -o Eta_expand.exe
	./Eta_expand.exe

all: eta_expand

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *.exe
	rm -f *~

