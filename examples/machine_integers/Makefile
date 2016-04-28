ULIB_ML=../../ulib/ml
OCAMLOPT=ocamlfind opt -thread -package batteries,stdint,zarith -linkpkg -g ../../ulib/ml/fstarlib.cmxa -I $(ULIB_ML)
INTS=$(addprefix ../../ulib/ml/, FStar_UInt_UInt8.ml FStar_UInt_UInt16.ml FStar_UInt_UInt32.ml FStar_UInt_UInt63.ml FStar_UInt_UInt64.ml FStar_Int_Int8.ml FStar_Int_Int16.ml FStar_Int_Int32.ml FStar_Int_Int63.ml FStar_Int_Int64.ml)

.PHONY:test

test:
	make -C $(ULIB_ML)
	$(OCAMLOPT) $(INTS) test.ml -o ints.exe
	./ints.exe

clean:
	make -C $(ULIB_ML) clean
	rm -rf ints.exe *~ *.o *.cmi *.cmo *.cmx
