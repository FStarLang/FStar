# FStar variables
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

KREMLIN_HOME=../../../kremlin
KREMLIN=$(KREMLIN_HOME)/Kremlin.native
KREMLIN_ARGS=-tmpdir kremlin -verbose --lax

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info

CURVE_ODIR=curve
CHACHA_ODIR=chacha
POLY_ODIR=poly
AEAD_ODIR=aead

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26

REALIZED_MLI=
REALIZED=FStar_HST Low_Bytes FStar_HST_Monotonic_RRef #FStar_HyperStack 
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , FStar.Buffer SInt $(REALIZED_MODULE))

CURVE_EXTRACTED=FStar_TSet.ml FStar_FunctionalExtensionality.ml FStar_Ghost.ml Math_Axioms.ml Math_Lib.ml Math_Definitions.ml Math_Field.ml Math_Curve.ml Curve_Parameters.ml Curve_Bigint.ml Curve_Fsum.ml Curve_FsumWide.ml Curve_Fdifference.ml Curve_Fscalar.ml Curve_Fproduct.ml Curve_Modulo.ml Curve_Bignum.ml Curve_Crecip.ml Curve_Point.ml Curve_AddAndDouble.ml Curve_Ladder.ml
CHACHA_EXTRACTED=Buffer_Utils.ml Crypto_Symmetric_Chacha20.ml
POLY_EXTRACTED=FStar_List_Tot.ml FStar_Ghost.ml FStar_Seq.ml Buffer_Utils.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305.ml
AEAD_EXTRACTED= FStar_List_Tot.ml FStar_Seq.ml Buffer_Utils.ml Crypto_Symmetric_Chacha20.ml FStar_Ghost.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305_Lemmas.ml Crypto_Symmetric_Poly1305.ml Crypto_Symmetric_Poly1305_MAC.ml Crypto_AEAD_Chacha20Poly1305.ml

.PHONY: lib-ver curve-ver curve-ml chacha-ver chacha-ml ulib

all: uall sall

uall:
	+make clean
	+make chacha-test poly-test aead-test curve-test

sall:

ulib: $(FSTAR_HOME)/ulib/ml/fstarlib.cmxa

$(FSTAR_HOME)/ulib/ml/fstarlib.cmxa:
	make -j 1 -C $(FSTAR_HOME)/ulib/ml clean all

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) FStar.HyperStack.fst FStar.HST.fst FStar.Buffer.fst

# Curve25519 lax typechecking
curve-lax:
	$(FSTAR) Curve.Crecip.fst Curve.Ladder.fst --lax

# Curve25519 extraction to OCaml
curve-extract: ulib
	mkdir -p $(CURVE_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include crypto crypto/Curve.Crecip.fst crypto/Curve.Ladder.fst --odir $(CURVE_ODIR) #2> /dev/null
	@sed -i.bak 's/(Obj.magic ((fun pp ppq p pq q n ctr b scalar/(((fun pp ppq p pq q n ctr b scalar/g' $(CURVE_ODIR)/Curve_Ladder.ml

curve-compile: curve-extract
	$(OCAMLOPT) -I crypto/ml -I $(CURVE_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(CURVE_ODIR)/,$(CURVE_EXTRACTED)) crypto/ml/test_curve.ml -o test_curve.exe

curve-test: curve-compile
	./test_curve.exe

# AES targets
chacha-ver:
	$(FSTAR) Chacha.fst 

chacha-extract: ulib
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include crypto crypto/Crypto.Symmetric.Chacha20.fst --odir $(CHACHA_ODIR) 

chacha-compile: chacha-extract
	$(OCAMLOPT) -I crypto/ml -I $(CHACHA_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) crypto/ml/test_chacha.ml -o test_chacha.exe

chacha-test: chacha-compile
	./test_chacha.exe

poly-extract: ulib
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include crypto crypto/Crypto.Symmetric.Poly1305.fst --odir $(POLY_ODIR) #2> /dev/null
	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(POLY_ODIR)/Crypto_Symmetric_Poly1305.ml

poly-compile: poly-extract
	$(OCAMLOPT) -I crypto/ml -I $(POLY_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) crypto/ml/test_poly.ml -o test_poly.exe

poly-test: poly-compile
	./test_poly.exe

aead-extract: ulib
	mkdir -p $(AEAD_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) --include crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst --odir $(AEAD_ODIR) #2> /dev/null
	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(AEAD_ODIR)/Crypto_Symmetric_Poly1305.ml

aead-compile: aead-extract
	$(OCAMLOPT) -I crypto/ml -I $(AEAD_ODIR) $(addprefix crypto/ml/,$(REALIZED_ML)) \
	  $(addprefix $(AEAD_ODIR)/,$(AEAD_EXTRACTED)) crypto/ml/test_aead.ml -o test_aead.exe

aead-test: aead-compile
	./test_aead.exe

chacha-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Chacha20.fst -skip-compilation

chacha-kremlin-test:
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Chacha20.fst $(addprefix $(KREMLIN_HOME)/test/, main-Chacha.c testlib.c) -o test_chacha.exe
	./test_chacha.exe

poly-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Poly1305.fst -skip-compilation

poly-kremlin-test:
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Poly1305.fst $(addprefix $(KREMLIN_HOME)/test/, main-Poly1305.c testlib.c) -o test_poly.exe
	./test_poly.exe

aead-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst -skip-compilation

aead-kremlin-test:
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst $(addprefix $(KREMLIN_HOME)/test/, main-Aead.c testlib.c) -o test_aead.exe
	./test_aead.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix crypto/ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CURVE_ODIR) $(CHACHA_ODIR) $(POLY_ODIR) $(AEAD_ODIR) kremlin *~ *.exe ./crypto/*~
