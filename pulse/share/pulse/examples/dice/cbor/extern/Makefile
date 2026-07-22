all: build

.PHONY: all build

build: CBOR.o

KRML_INCLUDE = $(shell "$(KRML_EXE)" -locate-include)
KRML_KRMLLIB = $(shell "$(KRML_EXE)" -locate-krmllib)

%.o: %.c
	$(CC) -Wall -I "$(KRML_INCLUDE)" -I "$(KRML_KRMLLIB)/dist/generic" -c -o $@ $<

CBOR.o: CBOR.h internal/CBOR.h
