TRACE=
ifeq ($(TRACE), true)
override OTHERFLAGS += --trace_error --prn
endif
PRN=
ifeq ($(PRN), true)
override OTHERFLAGS += --prn
endif


FSTAR=../../bin/FStar.exe --fstar_home ../../  $(OTHERFLAGS)

ALLFILES=utils list tuple rec pat letrec termination skel 

all: $(addprefix tc., $(ALLFILES)) pt-compiler

prims: 
	$(FSTAR) --pretype --prims prims.fst

tc.%: %.fst
	$(FSTAR) --pretype --prims prims.fst $^


STDFILES=list.fst string.fst
BASICFILES=bytes.fst util.fst getoptsimple.fst options.fs range.fst unionfind.fst
BASIC=$(addprefix ../../src/basic/, $(BASICFILES))
SYNTAXFILES=syntax.fs const.fs visit.fs util.fs print.fs
SYNTAX=$(addprefix ../../src/absyn/, $(SYNTAXFILES))
PARSERFILES=ast.fs dsenv.fsi dsenv.fs desugar.fsi desugar.fs parse.fst lexhelp.fs parseit.fst driver.fs 
PARSER=$(addprefix ../../src/parser/, $(PARSERFILES))
TCFILES=errors.fs tcenv.fsi tcenv.fs normalize.fsi normalize.fs rel.fsi rel.fs tcutil.fsi tcutil.fs tc.fs
TC=$(addprefix ../../src/tc/, $(TCFILES))
MAINFILES=fstar.fs
MAIN=$(addprefix ../../src/, $(MAINFILES))
ALL=prims.fst st.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(TC) $(MAIN)

pt-compiler:
	$(FSTAR) --pretype --prims prims.fst st.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(TC)

compiler:
	$(FSTAR) --prims prims.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) backends.fsi $(MAIN)

wc: $(ALL)
	wc -l $^

clean:
	rm *~ 
