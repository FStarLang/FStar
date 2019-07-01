FSTAR_HOME=../..

include ../Makefile.include

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: hello testseq

hello: out Hello.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Hello' Hello.fst --record_hints
	$(OCAMLOPT) out/Hello.ml -o hello.exe
	./hello.exe

testseq: out TestSeq.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'TestSeq' TestSeq.fst --record_hints
	$(OCAMLOPT) out/TestSeq.ml -o testseq.exe
	./testseq.exe

out:
	mkdir -p out

clean:
	rm -rf out *~ *.exe
