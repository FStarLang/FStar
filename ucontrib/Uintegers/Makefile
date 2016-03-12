.PHONY: all verify build clean

all: verify build

verify:
	$(FSTAR) fst/Uintegers.Uint8.fst
	$(FSTAR) fst/Uintegers.Uint16.fst
	$(FSTAR) fst/Uintegers.Uint32.fst
	$(FSTAR) fst/Uintegers.Uint64.fst

build:
	$(OCAML) $(OCAMLOPTIONS) -c ml/Uint8.ml
	$(OCAML) $(OCAMLOPTIONS) -c ml/Uint16.ml
	$(OCAML) $(OCAMLOPTIONS) -c ml/Uint32.ml
	$(OCAML) $(OCAMLOPTIONS) -c ml/Uint64.ml
	(cd ml; $(OCAML) $(OCAMLOPTIONSCMXA) Uint8.cmx Uint16.cmx Uint32.cmx Uint64.cmx -o Uintegers.cmxa)

clean:
	@rm -rf *.ml *.p.* *.cm* *.a *.o *~ *.out
	@(cd ml; rm -rf *.p.* *.cm* *.a *.o *~ *.out)

FSTAR=../../bin/fstar.exe
OCAML= ocamlfind ocamlopt
OCAMLOPTIONS= -package batteries,stdint -linkpkg -g -thread
OCAMLOPTIONSCMXA= -a -package batteries,stdint
