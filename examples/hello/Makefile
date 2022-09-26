include ../Makefile.include

include $(FSTAR_ULIB)/ml/Makefile.include

all: hello testseq multi strings

hello: out Hello/Hello.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Hello' Hello/Hello.fst --record_hints
	$(OCAMLOPT) out/Hello.ml -o hello.exe
	./hello.exe

testseq: out TestSeq/TestSeq.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'TestSeq' TestSeq/TestSeq.fst --record_hints
	$(OCAMLOPT) out/TestSeq.ml -o testseq.exe
	./testseq.exe

strings: out strings/TestStrings.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'TestStrings' strings/TestStrings.fst --record_hints
	$(OCAMLOPT) out/TestStrings.ml -o teststrings.exe

multi:
	$(MAKE) -C multifile

out:
	mkdir -p out

clean:
	rm -rf out *~ *.exe
