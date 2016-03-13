WARN=--warn 1 --nowarn 42 --nowarn 58
BASELIBS=-r FSharp.PowerPack.dll
FSTAR_SRC=prin.fine datamodel.fine policytypes.fine messages.fine externdb.fine auth.fine util.fine policy.fine healthdb.fine log.fine healthmgr.fine
FSTAR=fstar.exe --silent

all:: dirs healthweb

wc:
	wc $(FSTAR_SRC)

dirs:
	mkdir -p queries bin

healthweb-fstar: $(FSTAR_SRC)
	$(FSTAR) $(FSTAR_SRC)

healthweb_genil: $(FSTAR_SRC)
	$(FSTAR) --prims prims.f9 --genIL $(FSTAR_SRC)

healthweb_rdcil: $(FSTAR_SRC)
	$(FSTAR) --rdcil --genIL $(FSTAR_SRC)

healthweb: $(FSTAR_SRC)
	$(FSTAR) --odir bin --writePrims --genIL $(FSTAR_SRC)

healthweb-untypedpf: $(FSTAR_SRC)
	$(FSTAR) --extract_proofs --prooflibvals $(FSTAR_HOME)/prooflibvals.f9 $(FSTAR_SRC)

healthweb-pf: $(FSTAR_SRC)
	$(FSTAR) --odir bin --writePrims --genIL --typecheck_proofs --prooflibvals $(FSTAR_HOME)/prooflibvals.f9 $(FSTAR_SRC)

ext.dll:
	fsc -r prims.dll -r authentication.dll -r externdb.dll -r datamodel.dll ext.fs 

clean:
	rm -rf *.exe *.pdb *.dll *.conf *.il *~ queries/ out/
