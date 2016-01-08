# --------------------------------------------------------------------
ifeq ($(OS),Windows_NT)
MSBUILD = msbuild
else
MSBUILD = xbuild
endif

FSTAR_HOME = ../..
LIB_FILES= FStar.String.fst FStar.Set.fst FStar.Map.fst FStar.Heap.fst array.fst FStar.ST.fst array-realized.fst
STDLIB = FStar.List.fst $(addprefix $(FSTAR_HOME)/lib/, $(LIB_FILES))
#FSTAR      = ../../bin/fstar.exe --codegen OCaml --odir ocaml-gen  $(STDLIB) $(OTHERFLAGS)

#Use the following to test the bootstrapped ocaml version: fstarml
FSTAR      = ../../src/ocaml-output/fstarml --debug_level LOW --prims ../../lib/prims.fst  $(STDLIB) $(OTHERFLAGS)

STDCACHE=Prims.cache List.cache String.cache ST.cache PartialMap.cache Array.cache
FSTARC=../../bin/fstar.exe  $(STDCACHE) $(OTHERFLAGS)

all: all-lax all-ver

# removed rbtree.fst from this list for now as it takes more z3 time
# removed mergsort from this list for the same reason

VERFILES=unit1.fst testset.fst millionaires.fst listlemmas.fst intlist-insertionsort.fst insertionsort.fst insertionsort-lemma.fst sf-basic.fst sf-lists.fst termination.fst termination-bugs.fst cca2.fst sf-poly.fst format.fst mac.fst sig.fst stlc.fst qs.fst cca2.fst bug22.fst bug19.fst bug29.fst bug26.fst bug15.fst bug25.fst bug24.fst bug28.fst bug35.fst bug52.fst bug23.fst bug21.fst

acls2: FStar.List.fst $(addprefix $(FSTAR_HOME)/lib/, FStar.String.fst partialmap.fst FStar.ST.fst) acls2.fst
	../../bin/fstar.exe  $^ --verify

counters: FStar.List.fst $(addprefix $(FSTAR_HOME)/lib/, FStar.String.fst partialmap.fst stperm.fst) ../sep/counters.fst
	../../bin/fstar.exe  $^ --verify

test: $(addprefix $(FSTAR_HOME)/lib/, partialmap.fst FStar.ST.fst) test.fst
	../../bin/fstar.exe  $^ --verify $(OTHERFLAGS)

cache: $(STDLIB)
	mkdir $(FSTAR_HOME)/cache
	$(FSTAR) --serialize_mods --verify

map:
	../../bin/fstar.exe $(OTHERFLAGS) $(FSTAR_HOME)/lib/partialmap.fst --verify --logQueries

ccache:
	rm -f $(addprefix $(FSTAR_HOME)/cache/, $(STDCACHE))

rpc:
	$(FSTAR) $(OTHERFLAGS) mac.fst format.fst rpc.fst --verify
rpc2:
	$(FSTAR) $(OTHERFLAGS) mac2.fst format.fst rpc2.fst --verify

encrypt:
	$(FSTAR) mac.fst encrypt.fs
encrypt3:
	$(FSTAR) mac.fst encrypt3.fst

rbt:
	$(FSTAR) --z3timeout 10 --verify rbtree.fst

%.c.ver: %.fst
	$(FSTARC) --verify $^

all-ver: $(VERFILES)
	$(FSTAR) --verify $^

all-lax: rec.fst pat.fst mac.fst bug16.fst
	$(FSTAR) --lax $^

%.vv: FStar.List.fst %.fst
	../../bin/fstar.exe $(OTHERFLAGS)  $^ --verify

stlc:
	../../bin/fstar.exe $(OTHERFLAGS)  stlc.fst --verify

format: format.fst
	../../bin/fstar.exe $(OTHERFLAGS)  $(FSTAR_HOME)/lib/array-realized.fst format.fst --verify

mac: mac.fst
	../../bin/fstar.exe $(OTHERFLAGS)  $(FSTAR_HOME)/lib/FStar.List.fst $(FSTAR_HOME)/lib/array-realized.fst mac.fst --verify

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
