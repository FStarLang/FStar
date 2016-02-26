all: verify build

verify:
	$(FSTAR) fst/Uintegers.Uint8.fst
	$(FSTAR) fst/Uintegers.Uint16.fst
	$(FSTAR) fst/Uintegers.Uint32.fst
	$(FSTAR) fst/Uintegers.Uint64.fst

build:
	$(OCAML) $(OCAMLOPTIONS) -c ml/uintegers.ml

FSTAR=../../bin/fstar.exe
OCAML= ocamlfind ocamlopt
OCAMLOPTIONS= -package batteries,stdint -linkpkg -g -thread
