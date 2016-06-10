# FStar variables
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_VER=--universes
OPTIONS_OCAML=--lax --codegen OCaml --universes --no_location_info --use_native_int

CHACHA_ODIR=chacha20
POLY_ODIR=poly1305
CURVE_ODIR=curve25519
AES_ODIR=aes
SHA_ODIR=sha

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -I $(ULIB_ML)/native_int
REALIZED_MLI=SInt_UInt8 SInt_UInt32 SInt_UInt63 SInt_UInt64
REALIZED=SInt_Cast SBuffer SBytes
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED_MODULE))

CHACHA_EXTRACTED=Chacha.ml
POLY_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_Seq.ml FStar_Ghost.ml Axioms.ml Parameters.ml Bigint.ml Bignum.ml Poly.ml
CURVE_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_Seq.ml FStar_Ghost.ml Axioms.ml Bignum_Parameters.ml Bignum_Bigint.ml Bignum_Fsum.ml Bignum_FsumWide.ml Bignum_Fdifference.ml Bignum_Fscalar.ml Bignum_Fproduct.ml Bignum_Modulo.ml Bignum_Core.ml Curve_Point.ml Curve_AddAndDouble.ml Curve_Ladder.ml
AES_EXTRACTED=Crypto_AES.ml
SHA256_EXTRACTED=Crypto_Sha256.ml

.PHONY: lib-ver chacha-ver chacha-ml poly-ver poly-ml

all: lib-ver \
chacha-ver \
chacha-ml \
poly-ver \
poly-ml \
curve-lax \
curve-ml \
sha-lax \
sha-ml

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) $(OPTIONS_VER) sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SBytes.fst

# Verification target for CHACHA20
chacha-ver: 
	$(FSTAR) $(OPTIONS_VER) chacha.fst

# OCaml extracton of CHACHA20
chacha-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) chacha.fst --odir $(CHACHA_ODIR) 
	$(OCAMLOPT) -I ml -I $(CHACHA_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) ml/test_chacha20.ml -o test_chacha20.exe 
	./test_chacha20.exe

# Verification target for POLY1305
poly-ver:
	$(FSTAR) --universes sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SBytes.fst 
	$(FSTAR) --universes parameters.fst bigint.fst
	$(FSTAR) --universes bignum.fst
	$(FSTAR) --universes poly.fst

# OCaml extracton of POLY1305
poly-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) poly.fst --odir $(POLY_ODIR) #2> /dev/null
	$(OCAMLOPT) -I ml -I $(POLY_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) ml/test_poly1305.ml -o test_poly1305.exe 
	./test_poly1305.exe

# Curve25519 lax typechecking
curve-lax:
	$(FSTAR) $(OPTIONS_VER) Curve.Ladder.fst --lax

# Curve25519 extraction to OCaml
curve-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(CURVE_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Curve.Ladder.fst --odir $(CURVE_ODIR) #2> /dev/null
	@sed -i 's/(Obj.magic ((fun pp ppq p pq q n ctr b scalar/(((fun pp ppq p pq q n ctr b scalar/g' $(CURVE_ODIR)/Curve_Ladder.ml
	$(OCAMLOPT) -I ml -I $(CURVE_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CURVE_ODIR)/,$(CURVE_EXTRACTED)) ml/test_curve25519.ml -o test_curve25519.exe
	./test_curve25519.exe

# AES targets
aes-ver:
	$(FSTAR) $(OPTIONS_VER) Crypto.AES.fst --lax

aes-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(AES_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Crypto.AES.fst --odir $(AES_ODIR) 
	$(OCAMLOPT) -I ml -I $(AES_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED)) ml/test_aes.ml -o test_aes.exe
	./test_aes.exe

# SHA targets
sha256-ver:
	$(FSTAR) $(OPTIONS_VER) Crypto.Sha256.fst

sha256-lax:
	$(FSTAR) $(OPTIONS_VER) Crypto.Sha256.fst --lax

sha256-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(SHA_ODIR)256
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Crypto.Sha256.fst --odir $(SHA_ODIR)256
	$(OCAMLOPT) -I ml -I $(SHA_ODIR)256 $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(SHA_ODIR)256/,$(SHA256_EXTRACTED)) ml/test_sha256.ml -o test_sha256.exe
	./test_sha256.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) $(CHACHA_ODIR)_ml $(POLY_ODIR)_ml \
		$(BIGNUM_ODIR) $(CURVE_ODIR) $(AES_ODIR) *~ *.exe
