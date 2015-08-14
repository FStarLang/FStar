OCAMLC := ocamlfind ocamlopt
OCAMLLINK := ocamlfind ocamlopt
FLAGS := -g -ccopt -g
CMO := cmx

# If for some weird reason, you don't have ocamlfind installed, override it in
# your local config file.
-include Makefile.local

all: stacktest ffitest

stacktest: stack.o bitmask.o test.o
	$(OCAMLC) $(FLAGS) $^ -o $@

ffitest.$(CMO): camlstack.cmi

ffitest: camlstack.o stack.o bitmask.o ffitest.$(CMO)
	$(OCAMLLINK) $(FLAGS) -o $@ $^

%.cmi: %.mli
	$(OCAMLC) $(FLAGS) -c  $^ -o $@

%.$(CMO): %.ml
	$(OCAMLC) $(FLAGS) -c  $< -o $@

%.o: %.c
	$(OCAMLC) $(FLAGS) -c  $^ -o $@

clean:
	$(RM) *.o *.cm* stacktest ffitest
