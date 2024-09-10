FSTAR_EXAMPLES=$(realpath ../../examples)
include $(FSTAR_EXAMPLES)/Makefile.include
include $(FSTAR_ULIB)/ml/Makefile.include

all: inline_let all_cmi Eta_expand.test

%.exe: %.fst | out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml $<
	$(OCAMLOPT) out/$(patsubst %.fst,%.ml,$<) -o $@

%.test: %.exe
	$(call msg,RUN,$<)
	$(Q)./$<
	$(Q)touch $@

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
	rm -f *.exe *.test
	rm -f inline_let

