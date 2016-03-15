.PHONY: all verify build clean

all: verify build

verify:
	$(FSTAR) fst/UInt8.fst
	$(FSTAR) fst/UInt16.fst
	$(FSTAR) fst/UInt32.fst
	$(FSTAR) fst/UInt64.fst

build:
	$(OCAML) $(OCAMLOPTIONS) -c ml/UInt8.ml
	$(OCAML) $(OCAMLOPTIONS) -c ml/UInt16.ml
	$(OCAML) $(OCAMLOPTIONS) -c ml/UInt32.ml
	$(OCAML) $(OCAMLOPTIONS) -c ml/UInt64.ml
	(cd ml; $(OCAML) $(OCAMLOPTIONSCMXA) UInt8.cmx UInt16.cmx UInt32.cmx UInt64.cmx -o UIntegers.cmxa)

clean:
	@rm -rf *.ml *.p.* *.cm* *.a *.o *~ *.out
	@(cd ml; rm -rf *.p.* *.cm* *.a *.o *~ *.out)

FSTAR=../../bin/fstar.exe
OCAML= ocamlfind ocamlopt
OCAMLOPTIONS= -package batteries,stdint -linkpkg -g -thread
OCAMLOPTIONSCMXA= -a -package batteries,stdint
