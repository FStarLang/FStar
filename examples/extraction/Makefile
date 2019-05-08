FSTAR_HOME=../..
include ../Makefile.include
include $(FSTAR_HOME)/ulib/ml/Makefile.include

eta_expand: out Eta_expand.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Eta_expand.fst
	$(OCAMLOPT) out/Eta_expand.ml -o Eta_expand.exe
	./Eta_expand.exe

inline_let:
	$(FSTAR) --codegen OCaml InlineLet.fst
	egrep -A 10 test InlineLet.ml | grep -qs "17"

all: eta_expand inline_let all_cmi

all_cmi:
	$(MAKE) -C cmi all

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *.exe
	rm -f *~

