all: ../../bin/parse.exe

../../bin/parse.exe:  ast.fs parse.fs lexhelp.fs lex.fs dsenv.fs desugar.fs parseit.fsi parseit.fs driver.fs
	fsc --define:TEST -g -r ../../bin/tc.dll -r ../../bin/basic.dll -r ../../bin/absyn.dll --mlcompatibility $^ -o $@

parse.fs: parse.fsy
	fsyacc --module FStar.Parser.Parse $^

lex.fs: lex.fsl
	fslex --unicode $^

clean:
	rm lex.fs parse.fs

FSTAR_HOME ?= ../..

include ../Makefile.boot.common
