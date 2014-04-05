all: utils list tuple rec compiler

utils:
	fstar  --prims prims.fst utils.fst

list:
	fstar  --prims prims.fst list.fst

tuple:
	fstar --prims prims.fst tuple.fst

rec:
	fstar  --prims prims.fst rec.fst

STDFILES=list.fst string.fst
BASICFILES=bytes.fst util.fst getoptsimple.fsi options.fs range.fsi unionfind.fst
BASIC=$(addprefix ../../src/basic/, $(BASICFILES))
SYNTAXFILES=syntax.fs const.fs visit.fs util.fs print.fs 
SYNTAX=$(addprefix ../../src/absyn/, $(SYNTAXFILES))
PARSERFILES=ast.fs dsenv.fs desugar.fs parse.fst lexhelp.fs parseit.fsi driver.fs 
PARSER=$(addprefix ../../src/parser/, $(PARSERFILES))
MAINFILES=fstar.fs
MAIN=$(addprefix ../../src/, $(MAINFILES))
compiler:
	fstar --prims prims.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(MAIN)

wc: prims.fst utils.fst list.fst string.fst tuple.fst rec.fst ../../src/basic/util.fst ../../src/basic/options.fst ../../src/basic/range.fsi ../../src/basic/unionfind.fst $(SYNTAX) $(PARSER)
	wc -l $^

clean:
	rm *~ 
