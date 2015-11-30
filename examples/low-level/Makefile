ifdef WINDIR
EXE=.exe
else
EXE=
endif
FSTAR=fstar.exe $(OTHERFLAGS)

ALLOCATOR_DIR = ../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o $(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

OCAML = ocamlfind ocamlopt -g -package batteries -linkpkg -thread -I ../../src/ocaml-output/ -I $(ALLOCATOR_DIR) $(ALLOCATOR_FILES) ../../src/ocaml-output/support.ml

all:
	(cd lib; $(FSTAR) FStar.Regions.RST.fst)

Factorial.ml: factorial.fst
	$(FSTAR) --codegen OCaml $^
	./revertManualMLs.sh

PRE_SST_FILES=ListSet.ml Stack.ml FunctionalExtensionality.ml Ghost.ml Located.ml Lref.ml StackAndHeap.ml

# make Factorial.ml should build all the remailing .ml files
factorial$(EXE):  $(PRE_SST_FILES) SST.ml SSTCombinators.ml Factorial.ml Test.ml
	$(OCAML) -o $@ $^


MD5.ml: md5.fst
	$(FSTAR) MD5.fst
	./revertManualMLs.sh

md5$(EXE): $(PRE_SST_FILES) SST.ml SSTCombinators.ml MachineWord.ml Seq.ml SSTArray.ml ArrayAlgos.ml MD5Common.ml MD5.ml
	$(OCAML) -o $@ $^

Sieve.ml: sieve.fst
	$(FSTAR) --codegen OCaml $^
	./revertManualMLs.sh

ARRAY_FILES=Seq.ml SSTArray.ml ArrayAlgos.ml

sieve$(EXE): $(PRE_SST_FILES)  SST.ml SSTCombinators.ml $(ARRAY_FILES) SieveFun.ml Sieve.ml TestSieve.ml
	$(OCAML) -o $@ $^

#run make Sieve.ml, and make clean if you just made sieveLoopHeap
sieveLoop$(EXE): $(PRE_SST_FILES)  SST.ml SSTCombinators.ml $(ARRAY_FILES) SieveFun.ml Sieve.ml TestSieveInLoop.ml
	$(OCAML) $^ -o $@

#run make Sieve.ml
sieveLoopHeap$(EXE): $(PRE_SST_FILES)  SSTAllHeap.ml  SSTArrayAllHeap.ml SST.ml SSTCombinators.ml $(ARRAY_FILES) SieveFun.ml Sieve.ml TestSieveInLoop.ml
	cp SSTAllHeap.ml SST.ml
	cp SSTArrayAllHeap.ml SSTArray.ml
	$(OCAML) -o $@ $^

SieveFun.ml: sieveFun.fst
	$(FSTAR) --codegen OCaml $^
	./revertManualMLs.sh

sieveFun$(EXE): $(PRE_SST_FILES) SST.ml SSTCombinators.ml $(ARRAY_FILES) SieveFun.ml TestSieve.ml
	$(OCAML) -o $@ $^


LallocTest.ml: lallocTest.fst
	$(FSTAR) --codegen OCaml $^ --debug yes --prn
	./revertManualMLs.sh

lallocTest$(EXE): $(PRE_SST_FILES)  SST.ml LallocTest.ml TestLalloc.ml
	$(OCAML) -o $@ $^

support: #run this whenever the src file of cp is updated. It is tracked in git.
	cp ../../src/support/ocaml/fstar-lib/src/support.ml  ../../src/ocaml-output/

clean:
	rm *.cm* MD5.ml Sieve.ml Factorial.ml LallocTest.ml md5 factorial sieve SieveFun.ml ListSet.ml Stack.ml FunctionalExtensionality.ml Set.ml Ghost.ml StackAndHeap.ml SSTCombinators.ml MachineWord.ml Seq.ml ArrayAlgos.ml MD5Common.ml All.ml
	./revertManualMLs
