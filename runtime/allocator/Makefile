OCAMLC := ocamlfind ocamlc
OCAMLLINK := ocamlfind ocamlc -custom
FLAGS := -g

# If for some weird reason, you don't have ocamlfind installed, override it in
# your local config file.
-include Makefile.local

all: stacktest ffitest

stacktest: stack.o bitmask.o test.o
	$(OCAMLC) $(FLAGS) $^ -o $@

ffitest: camlstack.o stack.o bitmask.o camlstack.mli ffitest.o ffitest.ml
	$(OCAMLLINK) $(FLAGS) -o $@ $^

%.o: %.c
	$(OCAMLC) $(FLAGS) -c  $^ -o $@

clean:
	$(RM) *.o *.cm* stacktest ffitest
