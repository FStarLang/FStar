# FStar variables
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_VER=
OPTIONS_COMPILE=--lax --codegen C
OPTIONS_OCAML=--lax --codegen OCaml --universes --no_location_info --use_native_int

# C variables
CHACHA=chacha
POLY=poly
BIGNUM=bignum
CURVE=curve25519
AES=aes
SHA=sha256

CHACHA_ODIR=chacha20
POLY_ODIR=poly1305
BIGNUM_ODIR=bignum_library
CURVE_ODIR=curve25519
AES_ODIR=aes

CHACHA_C=Chacha.c test_chacha.c
POLY_C=Parameters.c Bignum.c Poly.c test_poly.c
BIGNUM_C=Bignum_Parameters.c Bignum_Fsum.c Bignum_FsumWide.c Bignum_Fdifference.c Bignum_Fscalar.c Bignum_Fproduct.c Bignum_Modulo.c Bignum_Core.c test_bignum.c
CURVE_C=Bignum_Parameters.c Bignum_Fsum.c Bignum_FsumWide.c Bignum_Fdifference.c Bignum_Fscalar.c Bignum_Fproduct.c Bignum_Modulo.c Bignum_Core.c Curve_Point.c Curve_AddAndDouble.c Curve_Ladder.c test_curve.c
AES_C=Crypto_AES.c test_aes.c

COMPILE=ocamlopt -ccopt -O3 fstarlib.c

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -I $(ULIB_ML)/native_int
REALIZED=SInt_UInt8 SInt_UInt32 SInt_UInt63 SInt_UInt64 SBuffer SBytes
REALIZED_ML=$(addsuffix .ml,$(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED))

POLY_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_Seq.ml FStar_Ghost.ml Axioms.ml Parameters.ml Bigint.ml Bignum.ml Poly.ml
CHACHA_OCAML=SInt_UInt8.ml SInt_UInt32.ml SBuffer.ml SBytes.ml Chacha.ml
SHA_X_OCAML=SInt.ml FStar_IO.ml FStar_Heap.ml SInt_UInt8.ml SInt_UInt32.ml SInt_UInt64.ml SBuffer.ml SBytes.ml

.PHONY: low-star-ver chacha-ver chacha-test poly-ver poly-test sha-ver sha-ml

all: chacha-test poly-test curve-test aes-test

low-star-ver:
	$(FSTAR) $(OPTIONS_VER) sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SBytes.fst

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
	cd $(CHACHA_ODIR)_ml && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(CHACHA_OCAML) test_chacha20.ml
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

poly-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) poly.fst --odir $(POLY_ODIR) #2> /dev/null
	$(OCAMLOPT) -I ml -I $(POLY_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) ml/test_poly1305.ml -o test_poly1305.exe
	./test_poly1305.exe

poly-ml-compile:
	cp ./ml/*.ml $(POLY_ODIR)_ml
	cd $(POLY_ODIR)_ml && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(POLY_OCAML) test_poly1305.ml

bignum-ver:
	$(FSTAR) $(OPTIONS_VER) Bignum.Core.fst --lax

bignum-test: Bignum.Core.fst
	@echo ""
	@echo " Extracting BIGNUM library "
	@mkdir -p $(BIGNUM_ODIR)
	$(FSTAR) $(OPTIONS_COMPILE) --odir $(BIGNUM_ODIR) $^
	@cp ./c/*.c ./c/*.h $(BIGNUM_ODIR)
	@echo ""
	@echo " Compiling BIGNUM"
	cd $(BIGNUM_ODIR) && $(COMPILE) $(BIGNUM_C) -o $(BIGNUM)
	./$(BIGNUM_ODIR)/$(BIGNUM)

bignum-debug: Bignum.Core.fst
	@cp ./c/*.c ./c/*.h $(BIGNUM_ODIR)
	@echo ""
	@echo " Compiling BIGNUM"
	cd $(BIGNUM_ODIR) && $(COMPILE) $(BIGNUM_C) -o $(BIGNUM)
	./$(BIGNUM_ODIR)/$(BIGNUM)


# Curve targets
curve-ver:
	$(FSTAR) $(OPTIONS_VER) Curve.Ladder.fst --lax

curve-test: Curve.Ladder.fst
	@echo ""
	@echo " Extracting CURVE library "
	@mkdir -p $(CURVE_ODIR)
	$(FSTAR) $(OPTIONS_COMPILE) --odir $(CURVE_ODIR) $^
	@cp ./c/*.c ./c/*.h $(CURVE_ODIR)
	@echo ""
	@echo " Compiling CURVE"
	cd $(CURVE_ODIR) && $(COMPILE) $(CURVE_C) -o $(CURVE)
	./$(CURVE_ODIR)/$(CURVE)

curve-debug: Curve.Ladder.fst
	@cp ./c/*.c ./c/*.h $(CURVE_ODIR)
	@echo ""
	@echo " Compiling CURVE"
	cd $(CURVE_ODIR) && $(COMPILE) $(CURVE_C) -o $(CURVE)
	./$(CURVE_ODIR)/$(CURVE)

# AES targets
aes-ver:
	$(FSTAR) $(OPTIONS_VER) Crypto.AES.fst --lax

aes-test: Crypto.AES.fst
	@echo ""
	@echo " Extracting AES library "
	@mkdir -p $(AES_ODIR)
	$(FSTAR) $(OPTIONS_COMPILE) --odir $(AES_ODIR) $^
	@cp ./c/*.c ./c/*.h $(AES_ODIR)
	@echo ""
	@echo " Compiling AES"
	cd $(AES_ODIR) && $(COMPILE) $(AES_C) -o $(AES)
	./$(AES_ODIR)/$(AES)

aes-debug: Crypto.AES.fst
	@cp ./c/*.c ./c/*.h $(AES_ODIR)
	@echo ""
	@echo " Compiling AES"
	cd $(AES_ODIR) && $(COMPILE) $(AES_C) -o $(AES)
	./$(AES_ODIR)/$(AES)



# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) $(CHACHA_ODIR)_ml $(POLY_ODIR)_ml \
		$(BIGNUM_ODIR) $(CURVE_ODIR) $(AES_ODIR) *~ *.exe
