FINE_COMPILER=fstar --silent
WARN=--warn 1 --nowarn 42 --nowarn 58
BASELIBS=-r FSharp.PowerPack.dll
ADDITIONAL=prims.f9 
FINE_SRC=auth.fine externdb.fine policytypes.fine healthdb.fine externnet.fine policy.fine healthmgr.fine
FINE=$(FINE_COMPILER) 

all:: dirs healthweb_rdcil

dirs:
	mkdir -p queries

testanf:
	$(FINE) --skip_translation --anf testanf.fine 

noanf:
	$(FINE) --skip_translation noanf.fine 

healthweb: $(FINE_SRC)
	$(FINE) --skip_translation $(FINE_SRC)

derefine: $(FINE_SRC)
	$(FINE) $(FINE_SRC)

healthweb.exe: $(FINE_SRC)
	$(FINE) --writePrims --genIL --skip_target_checker $(FINE_SRC)

healthwebil: $(FINE_SRC)
	$(FINE) --typecheck_proofs --genIL  $(FINE_HOME)/prooflibvals.f9 $(FINE_SRC)

healthweb_genil: $(FINE_SRC)
	$(FINE) --genIL --prims ../prims.f9  $(FINE_SRC)

healthweb_rdcil: $(FINE_SRC)
	$(FINE) --rdcil --genIL $(FINE_SRC)

healthwebnoproofs: $(FINE_SRC)
	$(FINE) --genIL  $(FINE_SRC)

clean:
	rm -rf *.exe *.pdb *.dll *.conf *.il *~ queries/ out/ dlls-* pfdlls-*
