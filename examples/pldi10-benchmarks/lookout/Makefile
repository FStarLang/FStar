WARN=--warn 1 --nowarn 42 --nowarn 58
BASELIBS=-r FSharp.PowerPack.dll
SRC=auth.fine datamodel.fine externs.fine lookoutrm.fine userpolicy.fine apptmaker.fine
FSTAR=fstar --silent

all:: dirs lookout_rdcil

dirs:
	mkdir -p queries

lookout: $(SRC)
	$(FSTAR) --noss --typecheck_proofs $(FINE_HOME)/prooflibvals.f9 $^

lookout_rdcil: $(SRC)
	$(FSTAR) --rdcil --genIL $(SRC)

clean:
	rm -rf *.exe *.pdb *.dll *.conf *.il *~ queries/ out/ dlls-* pfdlls-*
