all: CBORTest

.PHONY: all

.PHONY: CBORTest

CBORTest: .CBORTest.touch

.CBORTest.touch: CBORTest.exe
	./CBORTest.exe
	touch $@

KRML_INCLUDE = $(shell "$(KRML_EXE)" -locate-include)
KRML_KRMLLIB = $(shell "$(KRML_EXE)" -locate-krmllib)

CBORTest.o: CBORTest.c
	$(CC) -Werror -I "$(KRML_INCLUDE)" -I "$(KRML_KRMLLIB)/dist/generic" -I ../_output/ -c -o $@ $<

CBORTest.exe: CBORTest.o ../_output/CBOR_Pulse.o ../extern/CBOR.o
	$(CC) -o CBORTest.exe $^
