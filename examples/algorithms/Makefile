include ../Makefile.include

all: uall

uall: BinarySearch.uver IntSort.uver InsertionSort.uver MergeSort.uver QuickSort.List.uver QuickSort.Seq.uver GC.uver Unification.uver Huffman.uver QuickSort.Array.uver #downgrade  //TODO

downgrade: QuickSort.Array.fst downgrade.fst
	$(FSTAR) --include $(FSTAR_ULIB)/reclaimable downgrade.fst

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

out:
	mkdir -p out

# $ ocaml
#         OCaml version 4.03.0

# # #use "topfind";;
# - : unit = ()
# Findlib has been successfully loaded. Additional directives:
#   #require "package";;      to load a package
#   #list;;                   to list the available packages
#   #camlp4o;;                to load camlp4 (standard syntax)
#   #camlp4r;;                to load camlp4 (revised syntax)
#   #predicates "p,q,...";;   to set these predicates
#   Topfind.reset();;         to force that packages will be reloaded
#   #thread;;                 to enable threads

# - : unit = ()
# # #require "unix";;
# /Users/jonathan/.opam/4.03.0/lib/ocaml/unix.cma: loaded
# # #require "zarith";;
# /Users/jonathan/.opam/4.03.0/lib/zarith: added to search path
# /Users/jonathan/.opam/4.03.0/lib/zarith/zarith.cma: loaded
# # #require "stdint";;
# /Users/jonathan/.opam/4.03.0/lib/bytes: added to search path
# /Users/jonathan/.opam/4.03.0/lib/stdint: added to search path
# /Users/jonathan/.opam/4.03.0/lib/stdint/stdint.cma: loaded
# # #require "batteries";;
