FSTAR_HOME?=../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS)

OCAMLOPT=OCAMLPATH="$(FSTAR_HOME)/lib" ocamlfind opt

.PHONY: %.native %.interpreted
.PRECIOUS: %.fst.checked %.ml %.cmxs

all: CanonCommSemiring.interpreted CanonCommSemiring.native

%.fst.checked: %.fst
	$(FSTAR) --cache_checked_modules $*.fst

%.ml: %.fst.checked
	$(FSTAR) --codegen Plugin --extract $* $*.fst
	cat $*.ml.fixup >> $*.ml

%.cmxs: %.ml
	$(OCAMLOPT) -shared -package fstar.lib -o $@ $*.ml

# REMARK: --load will compile $*.ml if $*.cmxs does not exist, but we compile it before
%.native: %.cmxs
	$(FSTAR) --load $* $*.Test.fst

%.interpreted: %.fst.checked
	$(FSTAR) $*.Test.fst

clean:
	rm -f *.checked *.ml *.o *.cm[ix] *.cmxs *~
