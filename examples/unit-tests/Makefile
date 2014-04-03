all: utils list tuple rec compiler

utils:
	fstar  --prims prims.fst utils.fst

list:
	fstar  --prims prims.fst list.fst

tuple:
	fstar --prims prims.fst tuple.fst

rec:
	fstar  --prims prims.fst rec.fst

SYNTAXFILES=syntax.fs const.fs visit.fs util.fs print.fs 
SYNTAX=$(addprefix ../../src/absyn/, $(SYNTAXFILES))
PARSERFILES= #ast.fs #dsenv.fs desugar.fs driver.fs
PARSER=$(addprefix ../../src/parser/, $(PARSERFILES))
compiler:
	fstar  --prims prims.fst list.fst string.fst ../../src/basic/util.fst ../../src/basic/options.fst ../../src/basic/range.fsi ../../src/basic/unionfind.fst $(SYNTAX) $(PARSER)

wc: prims.fst utils.fst list.fst string.fst tuple.fst rec.fst ../../src/basic/util.fst ../../src/basic/options.fst ../../src/basic/range.fsi ../../src/basic/unionfind.fst $(SYNTAX) $(PARSER)
	wc -l $^

clean:
	rm *~ 
