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

all: $(addprefix tc., $(ALLFILES))

prims: 
	$(FSTAR) --pretype --prims prims.fst

tc.%: %.fst
	$(FSTAR) --pretype --prims prims.fst $^


STDFILES=list.fst string.fst
BASICFILES=bytes.fst util.fst getoptsimple.fsi options.fs range.fsi unionfind.fst
BASIC=$(addprefix ../../src/basic/, $(BASICFILES))
SYNTAXFILES=syntax.fs const.fs visit.fs util.fs print.fs
SYNTAX=$(addprefix ../../src/absyn/, $(SYNTAXFILES))
PARSERFILES=ast.fs dsenv.fs desugar.fs parse.fst lexhelp.fs parseit.fsi driver.fs 
PARSER=$(addprefix ../../src/parser/, $(PARSERFILES))
TCFILES=errors.fs tcenv.fs normalize.fs rel.fs tcutil.fs tc.fs
TC=$(addprefix ../../src/tc/, $(TCFILES))
MAINFILES=fstar.fs
MAIN=$(addprefix ../../src/, $(MAINFILES))
ALL=prims.fst st.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(TC) $(MAIN)

pt-compiler:
	$(FSTAR) --pretype --prims prims.fst st.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(TC)
#$(PARSER) $(TC)

compiler:
	$(FSTAR) --prims prims.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) backends.fsi $(MAIN)
#$(TC) 

wc: $(ALL)
	wc -l $^

clean:
	rm *~ 
