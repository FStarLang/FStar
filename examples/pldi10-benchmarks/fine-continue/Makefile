WARN=--warn 1 --nowarn 42 --nowarn 58
BASELIBS=-r FSharp.PowerPack.dll
COMMON_SRC=common.fs
SERVER_SRC=types.fs net.fs db.fs
FINE_SRC=externs.f9 serverrm.f9 servermain.f9
FINE=fstar --silent --to_dcil --rdcil

all:: dirs client.exe conf.dll server

dirs:
	mkdir -p queries
	mkdir -p data
	mkdir -p dll pfdll attrdll attrdll2

client.exe: $(COMMON_SRC) client.fs
	fsc -g $(WARN) -o client.exe $(BASELIBS) $(COMMON_SRC) client.fs --mlcompatibility

conf.dll: $(COMMON_SRC) $(SERVER_SRC)
	fsc --target library -g $(WARN) -o conf.dll $(BASELIBS) $^ --mlcompatibility

server_src: $(FINE_SRC)
	$(FINE) --to_dcil externs.f9 serverrm.f9 servermain.f9

server_pfs: $(FINE_SRC)
	$(FINE) --extract_proofs externs.f9 serverrm.f9 servermain.f9

server_check: $(FINE_SRC)
	$(FINE) --typecheck_proofs --prims ../../prims.f9 ../../prooflibvals.f9 externs.f9 serverrm.f9 servermain.f9

server_full: $(FINE_SRC)
	$(FINE) --to_dcil --typecheck_proofs --prims ../../prims.f9 ../../prooflibvals.f9 externs.f9 serverrm.f9 servermain.f9

server_noproofs: $(FINE_SRC)
	$(FINE) --odir dll --spl --genIL externs.f9 serverrm.f9 servermain.f9

server_il_attribs: $(FINE_SRC)
	$(FINE) --profile_attribs --odir attrdll --spl --genIL --pretty_attribs --pickle externs.f9 serverrm.f9 servermain.f9

server_il_attribs2: $(FINE_SRC)
	$(FINE) --profile_attribs --odir attrdll2 --spl --genIL --pretty_attribs --pickle externs.f9 serverrm.f9 servermain.f9

server_il: $(FINE_SRC)
	$(FINE) --odir pfdll --spl --genIL --typecheck_proofs --prims ../../prims.f9 externs.f9 serverrm.f9 servermain.f9

server_il_noss: $(FINE_SRC)
	$(FINE) --noss --odir pfdll --spl --genIL --typecheck_proofs externs.f9 serverrm.f9 servermain.f9

server_genil: $(FINE_SRC)
	$(FINE) --genIL --prims ../prims.f9 externs.f9 serverrm.f9 servermain.f9

server_rdcil: $(FINE_SRC)
	$(FINE) --rdcil --genIL --prims ../prims.f9 externs.f9 serverrm.f9 servermain.f9

server: $(FINE_SRC)
	$(FINE) externs.f9 serverrm.f9 servermain.f9

servermain.exe: $(FINE_SRC)
	$(FINE) --writePrims --genIL --skip_target_checker externs.f9 serverrm.f9 #servermain.f9

clean:
	rm -rf *.exe *.pdb *.dll *.conf *.il *~ queries/ out/ pfdlls-* dlls-*

