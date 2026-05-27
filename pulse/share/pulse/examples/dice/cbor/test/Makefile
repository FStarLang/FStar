all: CBORTest

.PHONY: all

.PHONY: CBORTest

CBORTest: .CBORTest.touch

.CBORTest.touch: CBORTest.exe
	./CBORTest.exe
	touch $@

CBORTest.o: CBORTest.c
	$(CC) -Werror -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I ../_output/ -c -o $@ $<

CBORTest.exe: CBORTest.o ../_output/CBOR_Pulse.o ../extern/CBOR.o
	$(CC) -o CBORTest.exe $^
