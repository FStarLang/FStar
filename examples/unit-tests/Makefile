# --------------------------------------------------------------------
ifeq ($(OS),Windows_NT)
RUNTIME =
MSBUILD = msbuild
else
RUNTIME = mono
MSBUILD = xbuild
endif

FSTAR_HOME = ../..
LIB_FILES=string.fst partialmap.fst st.fst array-realized.fst
STDLIB = list.fst $(addprefix $(FSTAR_HOME)/lib/, $(LIB_FILES))
FSTAR      = $(RUNTIME) ../../bin/fstar.exe --fstar_home $(FSTAR_HOME) $(STDLIB) $(OTHERFLAGS)

STDCACHE=Prims.cache List.cache String.cache ST.cache PartialMap.cache Array.cache
FSTARC=$(RUNTIME) ../../bin/fstar.exe --fstar_home $(FSTAR_HOME) $(STDCACHE) $(OTHERFLAGS)

all: all-lax all-ver

# removed rbtree.fst from this list for now as it takes more z3 time
# removed mergsort from this list for the same reason 

VERFILES=unit1.fst testset.fst millionaires.fst listlemmas.fst intlist-insertionsort.fst insertionsort.fst insertionsort-lemma.fst sf-basic.fst sf-lists.fst termination.fst termination-bugs.fst sf-poly.fst format.fst mac.fst sig.fst stlc.fst qs.fst cca2.fst bug34.fst bug22.fst bug19.fst bug29.fst bug26.fst bug15.fst bug25.fst bug24.fst bug28.fst bug35.fst bug52.fst bug23.fst bug21.fst

acls2: list.fst $(addprefix $(FSTAR_HOME)/lib/, string.fst partialmap.fst st.fst) acls2.fst
	$(RUNTIME) ../../bin/fstar.exe --fstar_home $(FSTAR_HOME) $^ --verify

counters: list.fst $(addprefix $(FSTAR_HOME)/lib/, string.fst partialmap.fst stperm.fst) ../sep/counters.fst
	$(RUNTIME) ../../bin/fstar.exe --fstar_home $(FSTAR_HOME) $^ --verify

test: $(addprefix $(FSTAR_HOME)/lib/, partialmap.fst st.fst) test.fst
	$(RUNTIME) ../../bin/fstar.exe --fstar_home $(FSTAR_HOME) $^ --verify $(OTHERFLAGS)

cache: $(STDLIB)
	mkdir $(FSTAR_HOME)/cache
	$(FSTAR) --serialize_mods --verify

map:
	$(RUNTIME) ../../bin/fstar.exe $(OTHERFLAGS) --fstar_home ../../ $(FSTAR_HOME)/lib/partialmap.fst --verify --logQueries

ccache:
	rm -f $(addprefix $(FSTAR_HOME)/cache/, $(STDCACHE))

rpc: 
	$(FSTAR) $(OTHERFLAGS) mac.fst format.fst rpc.fst --verify


rbt:
	$(FSTAR) --z3timeout 10 --verify rbtree.fst

%.c.ver: %.fst
	$(FSTARC) --verify $^

all-ver: $(VERFILES)
	$(FSTAR) --verify $^

all-lax: rec.fst pat.fst mac.fst bug16.fst
	$(FSTAR) --lax $^

%.vv: list.fst %.fst
	$(RUNTIME) ../../bin/fstar.exe $(OTHERFLAGS) --fstar_home $(FSTAR_HOME) $^ --verify

stlc:
	$(RUNTIME) ../../bin/fstar.exe $(OTHERFLAGS) --fstar_home $(FSTAR_HOME) stlc.fst --verify

format: format.fst
	$(RUNTIME) ../../bin/fstar.exe $(OTHERFLAGS) --fstar_home $(FSTAR_HOME) $(FSTAR_HOME)/lib/array-realized.fst format.fst --verify

mac: mac.fst
	$(RUNTIME) ../../bin/fstar.exe $(OTHERFLAGS) --fstar_home $(FSTAR_HOME) $(FSTAR_HOME)/lib/list.fst $(FSTAR_HOME)/lib/array-realized.fst mac.fst --verify

vector: vectors.fst
	$(FSTAR) --verify --full_context_dependency vectors.fst

wc-ver: $(STDLIB) $(VERFILES) rbtree.fst rpc.fst ../sep/counters.fst acls.fst acls2.fst
	wc -l $^

%.tc: %.fst
	$(FSTAR) $^

%.ver: %.fst
	$(FSTAR) --verify $^

prims: 
	$(FSTAR)  


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
