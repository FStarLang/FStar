# --------------------------------------------------------------------
ifeq ($(OS),Windows_NT)
RUNTIME =
MSBUILD = msbuild
else
RUNTIME = mono
MSBUILD = xbuild
endif

FSTAR_HOME = ../..
LIB_FILES=list.fst string.fst st.fst partialmap.fst array-realized.fst
STDLIB = $(addprefix $(FSTAR_HOME)/lib/, $(LIB_FILES))
FSTAR      = $(RUNTIME) ../../bin/fstar.exe --fstar_home $(FSTAR_HOME) $(STDLIB) $(OTHERFLAGS)

STDCACHE=Prims.cache List.cache String.cache ST.cache PartialMap.cache Array.cache
FSTARC=$(RUNTIME) ../../bin/fstar.exe --fstar_home $(FSTAR_HOME) $(STDCACHE) $(OTHERFLAGS)

all: all-lax all-ver

VERFILES=unit1.fst testset.fst millionaires.fst listlemmas.fst intlist-insertionsort.fst insertionsort.fst insertionsort-lemma.fst sf-basic.fst sf-lists.fst termination.fst termination-bugs.fst sf-poly.fst format.fst mac.fst bug34.fst bug22.fst bug19.fst bug29.fst bug26.fst bug15.fst bug25.fst bug24.fst bug28.fst bug35.fst

cache: $(STDLIB)
	mkdir $(FSTAR_HOME)/cache
	$(FSTAR) --serialize_mods --verify

ccache:
	rm -f $(addprefix $(FSTAR_HOME)/cache/, $(STDCACHE))

%.c.ver: %.fst
	$(FSTARC) --verify $^

all-ver: $(VERFILES)
	$(FSTAR) --verify $^

all-lax: rec.fst pat.fst mac.fst bug16.fst
	$(FSTAR) $^

%.vv: %.fst
	$(RUNTIME) ../../bin/fstar.exe $(OTHERFLAGS) --fstar_home $(FSTAR_HOME) $^ --verify

stlc:
	$(RUNTIME) ../../bin/fstar.exe $(OTHERFLAGS) --fstar_home $(FSTAR_HOME) stlc.fst --verify

format: format.fst
	$(RUNTIME) ../../bin/fstar.exe $(OTHERFLAGS) --fstar_home $(FSTAR_HOME) $(FSTAR_HOME)/lib/array-realized.fst format.fst --verify

mac: mac.fst
	$(RUNTIME) ../../bin/fstar.exe $(OTHERFLAGS) --fstar_home $(FSTAR_HOME) $(FSTAR_HOME)/lib/list.fst $(FSTAR_HOME)/lib/array-realized.fst mac.fst --verify

vector: vectors.fst
	$(FSTAR) --verify --full_context_dependency vectors.fst

wc-ver: $(STDLIB) $(VERFILES)
	wc -l $^

%.tc: %.fst
	$(FSTAR) $^

%.ver: %.fst
	$(FSTAR) --verify $^

prims: 
	$(FSTAR)  

test: 
	$(RUNTIME) ../../bin/fstar.exe $(OTHERFLAGS) --fstar_home $(FSTAR_HOME) test.fst --verify

utils:
	$(FSTAR) --codegen OCaml --prims prims.fst utils.fst

stdlib:
	$(FSTAR) --codegen OCaml $(STDLIB)

#NS: Moved the specifics from here to the mitls repo. 
#This target remains here just to not suprise anyone ... we should remove it soon.

# # Change the following line to the location of the top MITLS directory "lang-sec/msrc/cvk/samples/protocols/tls"
MITLS=../../../mitls
mitls:
	make -C $(MITLS)/ML mitls

wc-mitls:
	make -C $(MITLS)/ML wc

clean:
	rm *~ 
