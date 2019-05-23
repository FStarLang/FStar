# For simplified Makefiles, define FSTAR_HOME, then include the file below.
FSTAR_HOME=../..

include ../Makefile.include

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: hello testseq

hello: out hello.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Hello' hello.fst --record_hints
	$(OCAMLOPT) out/Hello.ml -o hello.exe
	./hello.exe

testseq: out testseq.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'TestSeq' testseq.fst --record_hints
	$(OCAMLOPT) out/TestSeq.ml -o testseq.exe
	./testseq.exe

out:
	mkdir -p out

clean:
	rm -rf out *~ *.exe
