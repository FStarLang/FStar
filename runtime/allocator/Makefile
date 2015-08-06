OCAMLC := ocamlfind ocamlc

# If for some weird reason, you don't have ocamlfind installed, override it in
# your local config file.
-include Makefile.local

all: stacktest ffitest

stacktest: stack.o bitmask.o test.o
	$(OCAMLC) $^ -o $@

ffitest: camlstack.o stack.o bitmask.o camlstack.mli ffitest.o ffitest.ml
	$(OCAMLC) -custom -o $@ $^

%.o: %.c
	$(OCAMLC) -g -c  $^ -o $@

clean:
	$(RM) *.o *.cm* stacktest ffitest
