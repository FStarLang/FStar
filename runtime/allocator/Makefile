all: stacktest ffitest

stacktest: stack.o bitmask.o test.o
	$(CC) $^ -o $@

ffitest: camlstack.o stack.o bitmask.o camlstack.mli ffitest.ml 
	ocamlc -custom -o $@ $^

%.o: %.c
	$(CC) -g -c -I`ocamlc -where` $^ -o $@

clean:
	$(RM) *.o *.cm* stacktest ffitest 