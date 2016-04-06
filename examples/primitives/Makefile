# FStar variables
FSTAR_HOME?=~/dev/FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

OPTIONS_VER=
OPTIONS_COMPILE=--lax --codegen C 
OPTIONS_OCAML=--lax --codegen OCaml --universes --no_location_info --use_native_int

# Low* variables
LOW_STAR_MODULES=Axioms IntLib IntLibLemmas SInt SInt.UInt8 SInt.UInt32 SInt.UInt63 SBuffer SBytes

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
SHA_X_ODIR=sha

CHACHA_C=Chacha.c test_chacha.c
POLY_C=Parameters.c Bignum.c Poly.c test_poly.c
BIGNUM_C=Bignum_Parameters.c Bignum_Fsum.c Bignum_FsumWide.c Bignum_Fdifference.c Bignum_Fscalar.c Bignum_Fproduct.c Bignum_Modulo.c Bignum_Core.c test_bignum.c
CURVE_C=Bignum_Parameters.c Bignum_Fsum.c Bignum_FsumWide.c Bignum_Fdifference.c Bignum_Fscalar.c Bignum_Fproduct.c Bignum_Modulo.c Bignum_Core.c Curve_Point.c Curve_AddAndDouble.c Curve_Ladder.c test_curve.c
AES_C=Crypto_AES.c test_aes.c
SHA_C=Crypto_Sha256.c

COMPILE=gcc -O4 fstarlib.c

# OCaml variables
OCAML=ocamlfind ocamlopt -package batteries,stdint -linkpkg -g -thread
DEBUG=ocamlfind ocamlc -package batteries,stdint -linkpkg -g -thread
OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/ulib/ml $(FSTAR_HOME)/ulib/ml/native_int)
#OCAML_LIB=$(addprefix $(FSTAR_HOME)/ulib/ml/, MkPrims.ml native_int/prims.ml FStar_Set.ml FStar_ST.ml FStar_All.ml) FStar_FunctionalExtensionality.ml FStar_Seq.ml FStar_Ghost.ml
OCAML_LIB=$(addprefix $(FSTAR_HOME)/ulib/ml/, fstarlib.cmxa) FStar_FunctionalExtensionality.ml FStar_Seq.ml FStar_Ghost.ml
CHACHA_OCAML=SInt_UInt8.ml SInt_UInt32.ml SBuffer.ml SBytes.ml Chacha.ml
POLY_OCAML=FStar_Heap.ml Axioms.ml SInt_UInt8.ml SInt_UInt32.ml SInt_UInt63.ml SInt_UInt64.ml SBuffer.ml SBytes.ml Parameters.ml Bigint.ml Bignum.ml Poly.ml
SHA_X_OCAML=SInt.ml FStar_IO.ml FStar_Heap.ml SInt_UInt8.ml SInt_UInt32.ml SInt_UInt64.ml SBuffer.ml SBytes.ml
NO_CODEGEN=$(addprefix --no_codegen , SInt SBytes Bigint Buffer SBuffer SInt_UInt32 SInt_UInt63 SInt_UInt64 SInt_UInt8)
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
	mkdir -p $(POLY_ODIR)_ml
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) poly.fst --odir $(POLY_ODIR)_ml #2> /dev/null
	cp ./ml/*.ml $(POLY_ODIR)_ml
	cd $(POLY_ODIR)_ml && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(POLY_OCAML) test_poly1305.ml 
	$(POLY_ODIR)_ml/a.out

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

# SHA targets
sha-ver:
	$(FSTAR) $(OPTIONS_VER) Crypto.Sha1.fst Crypto.Sha224.fst Crypto.Sha256.fst

sha1-ver:
	$(FSTAR) $(OPTIONS_VER) Crypto.Sha1.fst

sha1-ml:
	mkdir -p $(SHA_X_ODIR)1_ml
	$(FSTAR) $(OPTIONS_OCAML) $(FSTAR_LIB) Crypto.Sha1.fst --odir $(SHA_X_ODIR)1_ml
	cp ./ml/*.ml $(SHA_X_ODIR)1_ml

sha1-test: sha1-ml
	cd $(SHA_X_ODIR)1_ml && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(SHA_X_OCAML) Crypto_Sha1.ml test_sha1.ml -o test_sha1.out #2> /dev/null
	$(SHA_X_ODIR)1_ml/test_sha1.out

sha224-ver:
	$(FSTAR) $(OPTIONS_VER) Crypto.Sha224.fst

sha224-ml:
	mkdir -p $(SHA_X_ODIR)224_ml
	$(FSTAR) $(OPTIONS_OCAML) $(FSTAR_LIB) Crypto.Sha224.fst --odir $(SHA_X_ODIR)224_ml
	cp ./ml/*.ml $(SHA_X_ODIR)224_ml

sha224-test: sha224-ml
	cd $(SHA_X_ODIR)224_ml && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(SHA_X_OCAML) Crypto_Sha224.ml test_sha224.ml -o test_sha224.out #2> /dev/null
	$(SHA_X_ODIR)224_ml/test_sha224.out

sha256-ver:
	$(FSTAR) $(OPTIONS_VER) Crypto.Sha256.fst

sha256-ml:
	mkdir -p $(SHA_X_ODIR)256_ml
	$(FSTAR) $(OPTIONS_OCAML) $(FSTAR_LIB) Crypto.Sha256.fst --odir $(SHA_X_ODIR)256_ml
	cp ./ml/*.ml $(SHA_X_ODIR)256_ml

sha256-c: Crypto.Sha256.fst
	@echo ""
	@echo " Extracting SHA library "
	@mkdir -p $(SHA_X_ODIR)256
	$(FSTAR) $(OPTIONS_COMPILE) --odir $(SHA_X_ODIR)256 $^
	@cp ./c/*.c ./c/*.h $(SHA_X_ODIR)256

sha256-test: sha256-ml
	cd $(SHA_X_ODIR)256_ml && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(SHA_X_OCAML) Crypto_Sha256.ml test_sha256.ml -o test_sha256.out #2> /dev/null
	$(SHA_X_ODIR)256_ml/test_sha256.out

# Cleaning
clean:
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) $(CHACHA_ODIR)_ml $(POLY_ODIR)_ml \
		$(BIGNUM_ODIR) $(CURVE_ODIR) $(AES_ODIR) $(SHA_X_ODIR)* *~ *.exe
