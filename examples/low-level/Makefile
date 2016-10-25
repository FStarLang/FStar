FSTAR_HOME=../..

# using the hyperstack memory model, ulib/ml/Makefile.include used this variable to use appropriate ST files
MEM=HST

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)
CODEGEN_ARGS=--lax --codegen OCaml --no_location_info $(FSTAR_DEFAULT_ARGS)

KREMLIN_HOME=../../../kremlin
KREMLIN=$(KREMLIN_HOME)/Kremlin.native
KREMLIN_ARGS=-tmpdir kremlin -verbose --lax

CHACHA_ODIR=chacha
POLY_ODIR=poly
AEAD_ODIR=aead

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10

FSTAR_EXTRACT=$(FSTAR) $(CODEGEN_ARGS) --include $(FSTAR_HOME)/ulib/hyperstack --include crypto --include crypto/real

CHACHA_EXTRACTED=Buffer_Utils.ml Crypto_Symmetric_Chacha20.ml
POLY_EXTRACTED=FStar_List_Tot.ml FStar_Ghost.ml FStar_Seq.ml FStar_SeqProperties.ml Buffer_Utils.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Chacha20.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_Cipher.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305_Spec.ml Flag.ml Crypto_Symmetric_Poly1305.ml
AEAD_EXTRACTED=FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml Buffer_Utils.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Chacha20.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_Cipher.ml FStar_Ghost.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum.ml Flag.ml Crypto_Symmetric_Poly1305.ml FStar_Monotonic_RRef.ml Crypto_Symmetric_Poly1305_MAC.ml Crypto_AEAD_Chacha20Poly1305.ml
# TODO: temove FStar_BitVector below once it's no longer needed
CHACHA_AEAD_EXTRACTED=FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml FStar_BitVector.ml FStar_UInt.ml Buffer_Utils.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Chacha20.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_Cipher.ml FStar_Ghost.ml Flag.ml Plain.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305.ml FStar_Monotonic_RRef.ml Crypto_Symmetric_Poly1305_MAC.ml Crypto_Symmetric_PRF.ml Crypto_AEAD_Encoding.ml Crypto_AEAD_Invariant.ml Crypto_AEAD_Lemmas.ml Crypto_AEAD_Lemmas_Part2.ml Crypto_AEAD.ml

.PHONY: lib-ver chacha-ver chacha-ml ulib

#16-09-18 lib-ver works but is too slow/brittle? 
all: uall sall

uall:
	make clean
	+make chacha-test poly-test aead-test aes-test aesgcm-test chacha-aead-test
	+make -C crypto all

sall:

ulib: $(FSTAR_HOME)/ulib/ml/fstarlib.cmxa

$(FSTAR_HOME)/ulib/ml/fstarlib.cmxa:
	make -j 1 -C $(FSTAR_HOME)/ulib/ml MEM=HST clean all

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) FStar.HyperStack.fst FStar.HST.fst FStar.Buffer.fst


chacha-ver:
	$(FSTAR) Chacha.fst 

chacha-extract: ulib
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR_EXTRACT) crypto/Crypto.Symmetric.Chacha20.fst --odir $(CHACHA_ODIR) 

chacha-compile: chacha-extract
	$(OCAMLOPT) -I crypto/ml -I $(CHACHA_ODIR) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) \
	  crypto/ml/test_chacha.ml -o test_chacha.exe

chacha-test: chacha-compile
	./test_chacha.exe

poly-extract: ulib
	mkdir -p $(POLY_ODIR)
	$(FSTAR_EXTRACT) crypto/Crypto.Symmetric.Poly1305.fst --odir $(POLY_ODIR)
	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(POLY_ODIR)/Crypto_Symmetric_Poly1305.ml

poly-compile: poly-extract
	$(OCAMLOPT) -I crypto/ml -I $(POLY_ODIR) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) \
          crypto/ml/test_poly.ml -o test_poly.exe

poly-test: poly-compile
	./test_poly.exe

ideal-extract: ulib
	mkdir -p $(AEAD_ODIR)
	$(FSTAR_EXTRACT) crypto/Test.fst --odir $(AEAD_ODIR)
#	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(AEAD_ODIR)/Crypto_Symmetric_Poly1305.ml

ideal-compile: ideal-extract
	$(OCAMLOPT) -I crypto/ml -I $(AEAD_ODIR) \
	  $(addprefix $(AEAD_ODIR)/,$(AEAD_EXTRACTED)) \
	  -o test_ideal.exe

ideal-test: ideal-compile
	./test_ideal.exe

aead-extract: ulib
	mkdir -p $(AEAD_ODIR)
	$(FSTAR_EXTRACT) crypto/Crypto.AEAD.Chacha20Poly1305.fst --odir $(AEAD_ODIR)
	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(AEAD_ODIR)/Crypto_Symmetric_Poly1305.ml

aead-compile: aead-extract
	$(OCAMLOPT) -I crypto/ml -I $(AEAD_ODIR) \
	  $(addprefix $(AEAD_ODIR)/,$(AEAD_EXTRACTED)) \
	  crypto/ml/test_aead.ml -o test_aead.exe

aead-test: aead-compile
	./test_aead.exe

chacha-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Chacha20.fst -skip-compilation

chacha-kremlin-test:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Chacha20.fst $(addprefix $(KREMLIN_HOME)/test/, main-Chacha.c testlib.c) -o test_chacha.exe
	./test_chacha.exe

poly-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Poly1305.fst -skip-compilation

poly-kremlin-test:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Poly1305.fst $(addprefix $(KREMLIN_HOME)/test/, main-Poly1305.c testlib.c) -o test_poly.exe
	./test_poly.exe

aead-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst -skip-compilation

aead-kremlin-test:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst $(addprefix $(KREMLIN_HOME)/test/, main-Aead.c testlib.c) -o test_aead.exe
	./test_aead.exe

aes-ver:
	$(FSTAR) Crypto.Symmetric.AES.fst 

AES_ODIR=aes
AES_EXTRACTED=Crypto_Symmetric_AES.ml

aes-extract: ulib
	mkdir -p $(AES_ODIR)
	$(FSTAR_EXTRACT) crypto/Crypto.Symmetric.AES.fst --odir $(AES_ODIR) 

aes-compile: aes-extract
	$(OCAMLOPT) -I crypto/ml -I $(AES_ODIR) \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED)) \
	  crypto/ml/test_aes256.ml -o test_aes256.exe

aes-test: aes-compile
	./test_aes256.exe


AESGCM_ODIR=aesgcm
AESGCM_EXTRACTED=FStar_List_Tot.ml FStar_Ghost.ml FStar_Seq.ml FStar_SeqProperties.ml Buffer_Utils.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_GF128.ml Crypto_Symmetric_GCM.ml Crypto_AEAD_AES256GCM.ml

aesgcm-extract: ulib
	mkdir -p $(AESGCM_ODIR)
	$(FSTAR_EXTRACT) crypto/Crypto.AEAD.AES256GCM.fst --odir $(AESGCM_ODIR) 

aesgcm-compile: aesgcm-extract
	$(OCAMLOPT) -I crypto/ml -I $(AESGCM_ODIR) \
	  $(addprefix $(AESGCM_ODIR)/,$(AESGCM_EXTRACTED)) \
	  crypto/ml/test_aes_gcm.ml -o test_aes_gcm.exe

aesgcm-test: aesgcm-compile
	./test_aes_gcm.exe


CHACHA_AEAD_ODIR=chacha_aead

chacha-aead-extract: ulib
	mkdir -p $(CHACHA_AEAD_ODIR)
	$(FSTAR_EXTRACT) crypto/Test.fst --odir $(CHACHA_AEAD_ODIR)
	@sed -i 's/^let mod.*/ /g' $(CHACHA_AEAD_ODIR)/FStar_UInt.ml ##HACK!--need to fix #310

chacha-aead-compile: chacha-aead-extract
	$(OCAMLOPT) -I crypto/ml -I $(CHACHA_AEAD_ODIR) \
	  $(addprefix $(CHACHA_AEAD_ODIR)/,$(CHACHA_AEAD_EXTRACTED)) \
	  $(CHACHA_AEAD_ODIR)/Test.ml -o test_chacha_aead.exe

chacha-aead-test: chacha-aead-compile
	./test_chacha_aead.exe

bignum-ver:
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part5.fst --include crypto
	$(FSTAR) --use_hints --include crypto crypto/Crypto.Symmetric.Poly1305.Bignum.fst


# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix crypto/ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) $(AEAD_ODIR) $(AES_ODIR) $(AESGCM_ODIR) $(CHACHA_AEAD_ODIR) kremlin *~ *.exe ./crypto/*~
