FSTAR=../../bin/FStar.exe --fstar_home ../../

all: utils list tuple rec compiler

utils:
	$(FSTAR)  --prims prims.fst utils.fst

list:
	$(FSTAR)  --prims prims.fst list.fst

tuple:
	$(FSTAR) --prims prims.fst tuple.fst

rec:
	$(FSTAR)  --prims prims.fst rec.fst

STDFILES=list.fst string.fst
BASICFILES=bytes.fst util.fst getoptsimple.fsi options.fs range.fsi unionfind.fst
BASIC=$(addprefix ../../src/basic/, $(BASICFILES))
SYNTAXFILES=syntax.fs const.fs visit.fs util.fs print.fs 
SYNTAX=$(addprefix ../../src/absyn/, $(SYNTAXFILES))
PARSERFILES=ast.fs dsenv.fs desugar.fs parse.fst lexhelp.fs parseit.fsi driver.fs 
PARSER=$(addprefix ../../src/parser/, $(PARSERFILES))
TCFILES=tcenv.fs
TC=$(addprefix ../../src/tc/, $(TCFILES))
MAINFILES=fstar.fs
MAIN=$(addprefix ../../src/, $(MAINFILES))
ALL=$(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(TC) $(MAIN)

compiler:
	$(FSTAR) --prims prims.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(TC) $(MAIN)

wc: prims.fst $(ALL)
	wc -l $^

clean:
	rm *~ 
