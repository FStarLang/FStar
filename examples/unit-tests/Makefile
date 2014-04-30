FSTAR=../../bin/FStar.exe --fstar_home ../../

all: utils list tuple rec compiler

prims: 
	$(FSTAR) --pretype --prims prims.fst 

utils:
	$(FSTAR) --pretype --prims prims.fst utils.fst

list:
	$(FSTAR) --pretype  --prims prims.fst list.fst

tuple:
	$(FSTAR) --pretype --prims prims.fst tuple.fst

rec:
	$(FSTAR) --pretype --prims prims.fst rec.fst

pat:
	$(FSTAR) --pretype --prims prims.fst pat.fst

letrec:
	$(FSTAR) --pretype --prims prims.fst letrec.fst

STDFILES=list.fst string.fst
BASICFILES=bytes.fst util.fst getoptsimple.fsi options.fs range.fsi unionfind.fst
BASIC=$(addprefix ../../src/basic/, $(BASICFILES))
SYNTAXFILES=syntax.fs const.fs visit.fs util.fs print.fs 
SYNTAX=$(addprefix ../../src/absyn/, $(SYNTAXFILES))
PARSERFILES=ast.fs dsenv.fs desugar.fs parse.fst lexhelp.fs parseit.fsi driver.fs 
PARSER=$(addprefix ../../src/parser/, $(PARSERFILES))
TCFILES=errors.fs tcenv.fs tcutil.fs pretype.fs
TC=$(addprefix ../../src/tc/, $(TCFILES))
MAINFILES=fstar.fs
MAIN=$(addprefix ../../src/, $(MAINFILES))
ALL=$(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(TC) $(MAIN)

pt-compiler:
	$(FSTAR) --prn --pretype --prims prims.fst st.fst $(STDFILES) $(BASIC) $(SYNTAX)

compiler:
	$(FSTAR) --prims prims.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(TC) backends.fsi $(MAIN)

wc: prims.fst $(ALL)
	wc -l $^

clean:
	rm *~ 
