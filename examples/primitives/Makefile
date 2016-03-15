# FStar variables
FSTAR_HOME=~/dev/FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

OPTIONS_VER= 
OPTIONS_COMPILE=--lax --codegen C
OPTIONS_OCAML=--lax --codegen OCaml

# Low* variables
LOW_STAR_MODULES=Axioms IntLib IntLibLemmas Sint FStar.UInt8 FStar.UInt32 FStar.UInt63 SBuffer FStar.SBytes

# C variables
CHACHA=chacha
POLY=poly
CHACHA_ODIR=chacha20
POLY_ODIR=poly1305
CHACHA_C=Chacha.c test_chacha.c
POLY_C=Parameters.c Bignum.c Poly.c test_poly.c

COMPILE=gcc -O2 fstarlib.c 

# OCaml variables
OCAML=ocamlfind ocamlopt -package batteries -linkpkg -g -thread
DEBUG=ocamlfind ocamlc -package batteries -linkpkg -g -thread
OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml)
OCAML_LIB=$(addprefix $(FSTAR_HOME)/lib/ml/, MkPrims.ml native_int/prims.ml FStar_Set.ml FStar_ST.ml FStar_All.ml) FStar_FunctionalExtensionality.ml FStar_Seq.ml 
CHACHA_OCAML=FStar_UInt8.ml FStar_UInt32.ml SBuffer.ml FStar_SBytes.ml Chacha.ml

.PHONY: low-star-ver chacha-ver chacha-test poly-ver poly-test

all: chacha-test poly-test

low-star-ver:
	$(FSTAR) $(OPTIONS_VER) sbuffer.fst FStar.UInt8.fst FStar.UInt32.fst FStar.UInt63.fst FStar.SBytes.fst

chacha-ver: chacha.fst
	$(FSTAR) $(OPTIONS_VER) $^ --z3timeout 50 $(addprefix --verify_module , Chacha)

chacha-test: chacha.fst
	@echo ""
	@echo " Extracting CHACHA20"
	@mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(OPTIONS_COMPILE) --odir $(CHACHA_ODIR) $^
	@cp ./c/*.c ./c/*.h $(CHACHA_ODIR)
	@echo ""
	@echo " Compiling CHACHA20"
	cd $(CHACHA_ODIR) && $(COMPILE) $(CHACHA_C) -o $(CHACHA)
	./$(CHACHA_ODIR)/$(CHACHA)

chacha-ml:
	mkdir -p $(CHACHA_ODIR)_ml
	$(FSTAR) $(OPTIONS_OCAML) $(FSTAR_LIB) chacha.fst --odir $(CHACHA_ODIR)_ml
	cp ./ml/*.ml $(CHACHA_ODIR)_ml
	cd $(CHACHA_ODIR)_ml && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(CHACHA_OCAML) test_chacha20.ml #2>/dev/null
	$(CHACHA_ODIR)_ml/a.out

poly-ver: poly.fst
	$(FSTAR) $(OPTIONS_VER) $^ --z3timeout 250 $(addprefix --verify_module , Parameters Bigint Bignum Poly)

poly-test: poly.fst
	@echo ""
	@echo " Extracting POLY1305"
	@mkdir -p $(POLY_ODIR)
	$(FSTAR) $(OPTIONS_COMPILE) --odir $(POLY_ODIR) $^
	@cp ./c/*.c ./c/*.h $(POLY_ODIR)
	@echo ""
	@echo " Compiling POLY1305"
	cd $(POLY_ODIR) && $(COMPILE) $(POLY_C) -o $(POLY)
	./$(POLY_ODIR)/$(POLY)

poly1305-ml:
	mkdir -p $(POLY_ODIR)_ml
	$(FSTAR) $(OPTIONS_COMPILE) $(FSTAR_LIB) $(POLY1305) --odir $(POLY_ODIR)_ml
	cp ./ml/*.ml $(POLY_ODIR)
	cd $(POLY_ODIR) && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(POLY_OCAML)_ml test_poly1305.ml #2> /dev/null
	$(POLY_ODIR)/a.out

clean:
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) $(CHACHA_ODIR)_ml $(POLY_ODIR)_ml *~
