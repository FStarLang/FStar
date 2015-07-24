test: ffitest.o stack.o ffitest.ml
	 ocamlc -custom -o $@ $^

%.o: %.c
	$(CC) -c -I`ocamlc -where` $^ -o $@