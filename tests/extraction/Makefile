FSTAR_EXAMPLES=$(realpath ../../examples)
include $(FSTAR_EXAMPLES)/Makefile.include
include $(FSTAR_ULIB)/ml/Makefile.include

all: eta_expand inline_let all_cmi

eta_expand: out Eta_expand.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Eta_expand.fst
	$(OCAMLOPT) out/Eta_expand.ml -o Eta_expand.exe
	./Eta_expand.exe
	@touch $@

inline_let: InlineLet.fst
	$(FSTAR) --codegen OCaml InlineLet.fst
	egrep -A 10 test InlineLet.ml | grep -qs "17"
	@touch $@

all_cmi:
	+$(MAKE) -C cmi all

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *.exe
	rm -f *~
	rm -f eta_expand
	rm -f inline_let

