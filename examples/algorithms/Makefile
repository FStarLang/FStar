include ../Makefile.include

include $(FSTAR_ULIB)/ml/Makefile.include

all: uall

uall: BinarySearch.uver IntSort.uver InsertionSort.uver MergeSort.uver QuickSort.List.uver QuickSort.Seq.uver GC.uver Unification.uver Huffman.uver QuickSort.Array.uver IntervalIntersect.uver #downgrade  //TODO

downgrade: QuickSort.Array.fst downgrade.fst
	$(FSTAR) --include $(FSTAR_ULIB)/reclaimable downgrade.fst

# TODO: restore this OCaml extraction

include $(FSTAR_ULIB)/ml/Makefile.include

huffman-ocaml: out Huffman.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Huffman.fst
	$(OCAMLOPT) -I out out/FStar_List_Tot_Base.ml out/Huffman.ml -o Huffman.exe
	./Huffman.exe

OCAML_DEFAULT_FLAGS=
huffman-ocaml-repl: out Huffman.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Huffman.fst
	$(OCAMLC) -I out $(ULIB_ML)/prims.ml out/FStar_List_Tot_Base.ml out/Huffman.ml -o Huffman.exe        
	utop -I out -I $(ULIB_ML) Huffman.repl

intersect-ocaml: out IntervalIntersect.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'IntervalIntersect' IntervalIntersect.fst
	$(OCAMLOPT) out/IntervalIntersect.ml -o IntervalIntersect.exe
	./IntervalIntersect.exe

out:
	mkdir -p out
