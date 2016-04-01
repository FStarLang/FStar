# FStar variables
FSTAR_HOME?=~/dev/FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

OPTIONS_VER=
OPTIONS_COMPILE=--lax --codegen C
OPTIONS_OCAML=--lax --codegen OCaml

# Low* variables
LOW_STAR_MODULES=Axioms IntLib IntLibLemmas Sint FStar.UInt8 FStar.UInt32 FStar.UInt63 SBuffer FStar.SBytes

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
SHA_ODIR=sha256

CHACHA_C=Chacha.c test_chacha.c
POLY_C=Parameters.c Bignum.c Poly.c test_poly.c
BIGNUM_C=Bignum_Parameters.c Bignum_Fsum.c Bignum_FsumWide.c Bignum_Fdifference.c Bignum_Fscalar.c Bignum_Fproduct.c Bignum_Modulo.c Bignum_Core.c test_bignum.c
CURVE_C=Bignum_Parameters.c Bignum_Fsum.c Bignum_FsumWide.c Bignum_Fdifference.c Bignum_Fscalar.c Bignum_Fproduct.c Bignum_Modulo.c Bignum_Core.c Curve_Point.c Curve_AddAndDouble.c Curve_Ladder.c test_curve.c
AES_C=Crypto_AES.c test_aes.c
SHA_C=Crypto_Sha256.c

COMPILE=gcc -O4 fstarlib.c

# OCaml variables
OCAML=ocamlfind ocamlopt -package batteries -linkpkg -g -thread
DEBUG=ocamlfind ocamlc -package batteries -linkpkg -g -thread
OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml)
OCAML_LIB=$(addprefix $(FSTAR_HOME)/lib/ml/, MkPrims.ml native_int/prims.ml FStar_Set.ml FStar_ST.ml FStar_All.ml) FStar_FunctionalExtensionality.ml FStar_Seq.ml
CHACHA_OCAML=FStar_UInt8.ml FStar_UInt32.ml SBuffer.ml FStar_SBytes.ml Chacha.ml
POLY_OCAML=FStar_Heap.ml FStar_UInt8.ml FStar_UInt32.ml FStar_UInt63.ml SBuffer.ml FStar_SBytes.ml Parameters.ml Bigint.ml Bignum.ml Poly.ml
SHA_OCAML=Sint.ml FStar_Heap.ml FStar_UInt8.ml FStar_UInt32.ml FStar_UInt63.ml SBuffer.ml FStar_SBytes.ml Crypto_Sha256.ml

.PHONY: low-star-ver chacha-ver chacha-test poly-ver poly-test sha-ver sha-ml

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

poly-ml:
	mkdir -p $(POLY_ODIR)_ml
	$(FSTAR) $(OPTIONS_OCAML) $(FSTAR_LIB) poly.fst --odir $(POLY_ODIR)_ml
	cp ./ml/*.ml $(POLY_ODIR)_ml
	cd $(POLY_ODIR)_ml && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(POLY_OCAML) test_poly1305.ml #2> /dev/null
	$(POLY_ODIR)_ml/a.out

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
	$(FSTAR) $(OPTIONS_VER) Crypto.Sha256.fst

sha-ml:
	mkdir -p $(SHA_ODIR)_ml
	$(FSTAR) $(OPTIONS_OCAML) $(FSTAR_LIB) Crypto.Sha256.fst --odir $(SHA_ODIR)_ml
	cp ./ml/*.ml $(SHA_ODIR)_ml

sha-c: Crypto.Sha256.fst
	@echo ""
	@echo " Extracting SHA library "
	@mkdir -p $(SHA_ODIR)
	$(FSTAR) $(OPTIONS_COMPILE) --odir $(SHA_ODIR) $^
	@cp ./c/*.c ./c/*.h $(SHA_ODIR)

sha-test: sha-ml
	cd $(SHA_ODIR)_ml && $(OCAML) $(OCAML_INCLUDE_PATHS) $(OCAML_LIB) $(SHA_OCAML) test_sha256.ml #2> /dev/null
	$(SHA_ODIR)_ml/a.out

# Cleaning
clean:
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) $(CHACHA_ODIR)_ml $(POLY_ODIR)_ml $(SHA_ODIR)_ml \
		$(BIGNUM_ODIR) $(CURVE_ODIR) $(AES_ODIR) $(SHA_ODIR) *~ *.exe
