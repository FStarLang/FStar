OTHERFLAGS=

FSTAR_HOME=../..
include ../Makefile.include

all: uall sall

uall: BinarySearch.uver IntSort.uver InsertionSort.uver MergeSort.uver QuickSort.List.uver QuickSort.Seq.uver QuickSort.Array.uver GC.uver Unification.uver #downgrade //TODO
sall: counters.sver

downgrade: QuickSort.Array.fst downgrade.fst
	$(FSTAR) --include $(FSTAR_HOME)/ulib/reclaimable downgrade.fst --verify_module Downgrade

include $(FSTAR_HOME)/ulib/ml/Makefile.include

huffman-ocaml: out Huffman.fst
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Huffman.fst
	$(OCAMLOPT) -I out out/FStar_List_Tot.ml out/Huffman.ml -o Huffman.exe
	./Huffman.exe

# Very bad target
OCAML_DEFAULT_FLAGS=-I $(ULIB_ML)
huffman-ocaml-repl: out Huffman.fst
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Huffman.fst
	-$(OCAMLC) -I out out/FStar_List_Tot.ml out/Huffman.ml -o Huffman.exe
	cd ../../ulib/ml && ocamlfind ocamlc -package batteries,stdint,zarith -linkpkg -g prims.ml
	utop -I out -I ../../ulib/ml `ocamlfind query zarith`/zarith.cma ../../ulib/ml/prims.cmo out/FStar_List_Tot.cmo out/Huffman.cmo Huffman.repl

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
