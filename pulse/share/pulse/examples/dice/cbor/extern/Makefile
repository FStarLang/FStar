all: build

.PHONY: all build

build: CBOR.o

%.o: %.c
	$(CC) -Wall -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -c -o $@ $<

CBOR.o: CBOR.h internal/CBOR.h
