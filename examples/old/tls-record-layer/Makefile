FSTAR_HOME=../..

# using the hyperstack memory model, ulib/ml/Makefile.include used this variable to use appropriate ST files
MEM=HST

include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)
CODEGEN_ARGS=--lax --codegen OCaml --no_location_info $(FSTAR_DEFAULT_ARGS)

KRML_HOME?=../../../karamel
KRML=$(KRML_HOME)/Karamel.native
KRML_ARGS=-tmpdir karamel -cc clang

CHACHA_ODIR=chacha
POLY_ODIR=poly
AEAD_ODIR=aead

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10

FSTAR_EXTRACT=$(FSTAR) $(CODEGEN_ARGS) --include crypto --include crypto/real

CHACHA_EXTRACTED=Buffer_Utils.ml Crypto_Symmetric_Chacha20.ml
POLY_EXTRACTED=FStar_List_Tot_Base.ml FStar_Ghost.ml FStar_Seq_Base.ml FStar_Seq_Properties.ml FStar_Seq.ml Buffer_Utils.ml Crypto_Config.ml Crypto_Indexing.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part6.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305_Spec.ml Flag.ml Crypto_Symmetric_Poly1305.ml
AEAD_EXTRACTED=FStar_List_Tot_Base.ml FStar_Seq_Base.ml FStar_Seq_Properties.ml FStar_Seq.ml Buffer_Utils.ml  Crypto_Config.ml Crypto_Indexing.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Chacha20.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_AES128.ml Crypto_Symmetric_Cipher.ml FStar_Ghost.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part6.ml Crypto_Symmetric_Poly1305_Bignum.ml Flag.ml Crypto_Symmetric_Poly1305_Lemmas.ml Crypto_Symmetric_Poly1305.ml FStar_Monotonic_RRef.ml Crypto_Symmetric_Poly1305_MAC.ml Crypto_AEAD_Chacha20Poly1305.ml
# TODO: remove FStar_BitVector below once it's no longer needed
CHACHA_AEAD_EXTRACTED=Spartan.ml FStar_List_Tot_Base.ml FStar_Seq_Base.ml FStar_Seq_Properties.ml FStar_Seq.ml FStar_BitVector.ml FStar_UInt.ml Buffer_Utils.ml Crypto_Config.ml Crypto_Indexing.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Chacha20.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_AES128.ml Crypto_Symmetric_Cipher.ml FStar_Ghost.ml Flag.ml Crypto_Plain.ml Crypto_Symmetric_GF128_Spec.ml Crypto_Symmetric_GF128.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part6.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305_Lemmas.ml Crypto_Symmetric_Poly1305.ml FStar_Monotonic_RRef.ml Crypto_Symmetric_MAC.ml Crypto_Symmetric_UF1CMA.ml Crypto_Symmetric_PRF.ml Crypto_AEAD_Encoding.ml Crypto_AEAD_Invariant.ml Crypto_AEAD_Encrypt_Invariant.ml Crypto_AEAD_Wrappers_PRF.ml Crypto_AEAD_Wrappers_Encoding.ml Crypto_AEAD_Wrappers_CMA.ml Crypto_AEAD_BufferUtils.ml Crypto_AEAD_Enxor_Invariant.ml Crypto_AEAD_EnxorDexor.ml Crypto_AEAD_MAC_Wrapper_Invariant.ml Crypto_AEAD_Encrypt_Ideal_Invariant.ml Crypto_AEAD_Encrypt.ml Crypto_AEAD_Decrypt.ml Crypto_AEAD.ml

.PHONY: lib-ver chacha-ver chacha-ml ulib

#NS: 12/21, we decided to only check verification on each commit; a full test happens nightly using the extra target
all:
	+make -C crypto all

extra:
	make clean
	+make chacha-test aes-test aesgcm-test chacha-aead-test
	+make -C crypto all extra
# removed tests poly-test and aead-test, relying on older code.

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
	$(FSTAR_EXTRACT) crypto/Crypto.Indexing.fst crypto/Crypto.Symmetric.Poly1305.fst --odir $(POLY_ODIR)
	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(POLY_ODIR)/Crypto_Symmetric_Poly1305.ml

poly-compile: poly-extract
	$(OCAMLOPT) -I crypto/ml -I $(POLY_ODIR) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) \
          crypto/ml/test_poly.ml -o test_poly.exe

poly-test: poly-compile
	./test_poly.exe

ideal-extract: ulib
	mkdir -p $(AEAD_ODIR)
	$(FSTAR_EXTRACT) crypto/Crypto.Indexing.fst crypto/Crypto.Test.fst --odir $(AEAD_ODIR)
#	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(AEAD_ODIR)/Crypto_Symmetric_Poly1305.ml

ideal-compile: ideal-extract
	$(OCAMLOPT) -I crypto/ml -I $(AEAD_ODIR) \
	  $(addprefix $(AEAD_ODIR)/,$(AEAD_EXTRACTED)) \
	  -o test_ideal.exe

ideal-test: ideal-compile
	./test_ideal.exe

aead-extract: ulib
	mkdir -p $(AEAD_ODIR)
	$(FSTAR_EXTRACT) crypto/Crypto.Indexing.fst crypto/Crypto.AEAD.Chacha20Poly1305.fst --odir $(AEAD_ODIR)
	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(AEAD_ODIR)/Crypto_Symmetric_Poly1305.ml

aead-compile: aead-extract
	$(OCAMLOPT) -I crypto/ml -I $(AEAD_ODIR) \
	  $(addprefix $(AEAD_ODIR)/,$(AEAD_EXTRACTED)) \
	  crypto/ml/test_aead.ml -o test_aead.exe

aead-test: aead-compile
	./test_aead.exe

chacha-karamel-extract:
	mkdir -p karamel
	$(KRML) $(KRML_ARGS) -I crypto crypto/Crypto.Symmetric.Chacha20.fst -skip-compilation

chacha-karamel-test:
	mkdir -p karamel
	$(KRML) $(KRML_ARGS) -I crypto crypto/Crypto.Symmetric.Chacha20.fst $(addprefix $(KRML_HOME)/test/, main-Chacha.c ../krmllib/testlib.c) -o test_chacha.exe
	./test_chacha.exe

poly-karamel-extract:
	mkdir -p karamel
	$(KRML) $(KRML_ARGS) -I crypto crypto/real/Flag.fst crypto/Crypto.Symmetric.Poly1305.fst -skip-compilation

poly-karamel-test:
	mkdir -p karamel
	$(KRML) $(KRML_ARGS) -I crypto crypto/real/Flag.fst crypto/Crypto.Symmetric.Poly1305.fst $(addprefix $(KRML_HOME)/test/, main-Poly1305.c ../krmllib/testlib.c) -o test_poly.exe
	./test_poly.exe

aead-karamel-extract:
	mkdir -p karamel
	$(KRML) $(KRML_ARGS) -I crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst -skip-compilation

aead-karamel-test:
	mkdir -p karamel
	$(KRML) $(KRML_ARGS) -I crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst $(addprefix $(KRML_HOME)/test/, main-Aead.c ../krmllib/testlib.c) -o test_aead.exe
	./test_aead.exe

aes-ver:
	$(FSTAR) Crypto.Symmetric.AES.fst 

AES_ODIR=aes
AES_EXTRACTED=Crypto_Symmetric_AES.ml

aes-extract: ulib
	mkdir -p $(AES_ODIR)
	$(FSTAR_EXTRACT) --include crypto/hacl/ crypto/Crypto.Symmetric.AES.fst --odir $(AES_ODIR) 

aes-compile: aes-extract
	$(OCAMLOPT) -I crypto/ml -I $(AES_ODIR) \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED)) \
	  crypto/ml/test_aes256.ml -o test_aes256.exe

aes-test: aes-compile
	./test_aes256.exe


AESGCM_ODIR=aesgcm
AESGCM_EXTRACTED=FStar_List_Tot_Base.ml FStar_Ghost.ml FStar_Seq_Base.ml FStar_Seq_Properties.ml FStar_Seq.ml Buffer_Utils.ml Crypto_Config.ml Crypto_Indexing.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_GF128_Spec.ml Crypto_Symmetric_GF128.ml Crypto_Symmetric_GCM.ml Crypto_AEAD_AES256GCM.ml

aesgcm-extract: ulib
	mkdir -p $(AESGCM_ODIR)
	$(FSTAR_EXTRACT) --include crypto/hacl/ crypto/Crypto.AEAD.AES256GCM.fst --odir $(AESGCM_ODIR) 

aesgcm-compile: aesgcm-extract
	$(OCAMLOPT) -I crypto/ml -I $(AESGCM_ODIR) \
	  $(addprefix $(AESGCM_ODIR)/,$(AESGCM_EXTRACTED)) \
	  crypto/ml/test_aes_gcm.ml -o test_aes_gcm.exe

aesgcm-test: aesgcm-compile
	./test_aes_gcm.exe


CHACHA_AEAD_ODIR=chacha_aead

chacha-aead-extract: ulib
	mkdir -p $(CHACHA_AEAD_ODIR)
	$(FSTAR_EXTRACT) --include crypto/hacl/ crypto/Crypto.Test.fst --odir $(CHACHA_AEAD_ODIR)
#	@sed -i.bak 's/^let mod.*/ /g' $(CHACHA_AEAD_ODIR)/FStar_UInt.ml ##HACK!--need to fix #310

chacha-aead-compile: chacha-aead-extract
	$(OCAMLOPT) -I crypto/ml -I $(CHACHA_AEAD_ODIR) \
	  $(addprefix $(CHACHA_AEAD_ODIR)/,$(CHACHA_AEAD_EXTRACTED)) \
	  $(CHACHA_AEAD_ODIR)/Crypto_Test.ml -o test_chacha_aead.exe

chacha-aead-test: chacha-aead-compile
	./test_chacha_aead.exe

bignum-ver:
	$(FSTAR) --ext optimize_let_vc crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1.fst --include crypto
	$(FSTAR) --ext optimize_let_vc crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2.fst --include crypto
	$(FSTAR) --ext optimize_let_vc crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3.fst --include crypto
	$(FSTAR) --ext optimize_let_vc crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4.fst --include crypto
	$(FSTAR) --ext optimize_let_vc crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part5.fst --include crypto
	$(FSTAR) --ext optimize_let_vc crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part6.fst --include crypto
	$(FSTAR) --ext optimize_let_vc --include crypto crypto/Crypto.Symmetric.Poly1305.Bignum.fst

KRML_INCLUDES=$(addprefix -I ,spartan_aes crypto $(KRML_HOME)/krmllib $(KRML_HOME)/test)
ifeq ($(OS),Windows_NT)
  KRML_ARGS=-ccopts -maes $(KOPTS)
else
  KRML_ARGS=-ccopts -maes,-fPIC $(KOPTS)
endif
KRML=$(KRML_HOME)/krml $(KRML_ARGS) $(KRML_INCLUDES) 

spartan_aes/aes.o:
	make -C spartan_aes

extract-krml-test:
	$(FSTAR) --no_extract FStar.Math.Lib --no_extract FStar.HyperHeap --no_extract FStar.HyperStack --no_extract FStar.ST --no_extract FStar.Seq --no_extract FStar.UInt128 --no_extract FStar.Int128 --no_extract FStar.UInt64 --no_extract FStar.Int64 --no_extract FStar.UInt32 --no_extract FStar.Int32 --no_extract FStar.UInt16 --no_extract FStar.Int16 --no_extract FStar.UInt8 --no_extract FStar.Int8 --no_extract Crypto.AEAD.MAC_Wrapper.Invariant --trace_error --include spartan_aes --include crypto --include ../../../../everest/karamel/krmllib --include ../../../../everest/karamel/test --include D:/workspace/everest/karamel/krmllib crypto/spartan/Crypto.Config.fst crypto/real/Flag.fst crypto/Crypto.KrmlTest.fst

krml-test.exe: spartan_aes/aes.o crypto/*.fst
	# -bundle Crypto_KrmlTest=Flag,Crypto.*
	$(KRML) spartan_aes/aes.o crypto/spartan_stub.c \
                -no-prefix Crypto.KrmlTest \
		-dast \
	        -drop Crypto.Symmetric.GF128.Spec -drop Crypto.Symmetric.PRF \
                $(KRML_HOME)/test/../krmllib/testlib.c crypto/test_hacks.c \
                -tmpdir tmp -add-include '"testlib.h"' -o $@ \
                crypto/spartan/Crypto.Config.fst crypto/real/Flag.fst crypto/Crypto.KrmlTest.fst
	-./krml-test.exe #AR: 04/27: this fails, but the tests don't apparently use it. will raise a bug for this too.

ifeq ($(OS),Windows_NT)
  WINSOCK=,-lws2_32
else
  WINSOCK=
endif

test-perf.exe: crypto/test_perf.c krml-test.exe
	# Add this argument once someone writes a proper API for the Crypto
	# subsystem
	#-bundle Crypto_KrmlTest=Flag,Crypto.* 
	# Note: cannot share the tmp directory otherwise the Makefile in
	# LowCProvider (which does ar ../tmp/*.o) would pick up the wrong main
	$(KRML) tmp/out.krml -drop Crypto.KrmlTest \
                  -tmpdir tmp-test-perf -add-include '"testlib.h"' -o $@ \
                  $(KRML_HOME)/krmllib/testlib.c crypto/test_hacks.c \
                  crypto/test_perf.c spartan_aes/aes.o crypto/spartan_stub.c \
                  -ldopt -flto \
                  -ccopts -Ofast,-m64,-march=native,-mtune=native,-funroll-loops,-fomit-frame-pointer,-Wno-int-conversion \
                  -I $(KRML_HOME)/krmllib -I $(KRML_HOME)/test \
                  -I $(OPENSSL_HOME)/include -ldopts -L,$(OPENSSL_HOME)/lib,-L,$(OPENSSL_HOME),-lcrypto$(WINSOCK) $(CFLAGS)
	PATH=$(OPENSSL_HOME):"$(PATH)" \
	  LD_LIBRARY_PATH=$(OPENSSL_HOME):"$(LD_LIBRARY_PATH)" \
	  DYLD_LIBRARY_PATH=$(OPENSSL_HOME):"$(DYLD_LIBRARY_PATH)" ./test-perf.exe

OCAML_FILES=tmp/FStar_Squash.ml tmp/FStar_StrongExcludedMiddle.ml tmp/FStar_List_Tot_Base.ml \
		tmp/FStar_Seq_Base.ml \
		tmp/FStar_Classical.ml tmp/FStar_List_Tot_Properties.ml tmp/FStar_List_Tot.ml tmp/FStar_Seq_Properties.ml tmp/FStar_Seq.ml \
		tmp/FStar_Math_Lemmas.ml tmp/FStar_BitVector.ml tmp/FStar_UInt.ml \
		tmp/FStar_FunctionalExtensionality.ml \
		tmp/FStar_PropositionalExtensionality.ml tmp/FStar_PredicateExtensionality.ml \
		tmp/FStar_TSet.ml tmp/FStar_Ghost.ml \
		tmp/FStar_Bytes.ml tmp/Buffer_Utils.ml tmp/Crypto_Symmetric_Bytes.ml \
		tmp/Crypto_Symmetric_Poly1305_Spec.ml tmp/Crypto_Symmetric_Poly1305_Parameters.ml \
		tmp/Crypto_Symmetric_Poly1305_Bigint.ml tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml \
		tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml \
		tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml \
		tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml \
		tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml \
		tmp/FStar_Buffer_Quantifiers.ml \
		tmp/Crypto_Symmetric_AES.ml \
		tmp/Crypto_Symmetric_AES128.ml \
		tmp/Crypto_Symmetric_Chacha20.ml \
		tmp/Crypto_Config.ml \
		tmp/Crypto_Indexing.ml \
		tmp/Spartan.ml \
		tmp/Crypto_Symmetric_Cipher.ml \
		tmp/Crypto_Symmetric_GF128_Spec.ml \
		tmp/Crypto_Symmetric_Poly1305_Lemmas.ml \
		tmp/Flag.ml \
		tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part6.ml \
		tmp/Crypto_Symmetric_Poly1305_Bignum.ml \
		tmp/Crypto_Symmetric_Poly1305.ml \
		tmp/Crypto_Symmetric_GF128.ml \
		tmp/Crypto_Symmetric_MAC.ml \
		tmp/FStar_Monotonic_RRef.ml \
		tmp/Crypto_Symmetric_UF1CMA.ml \
		tmp/Crypto_Plain.ml \
		tmp/Crypto_Symmetric_PRF.ml \
		tmp/Crypto_AEAD_Encoding.ml \
		tmp/Crypto_AEAD_Wrappers.ml \
		tmp/Crypto_AEAD_Invariant.ml \
		tmp/Crypto_AEAD_Lemmas_Part2.ml \
		tmp/Crypto_AEAD_Lemmas.ml \
		tmp/Crypto_AEAD.ml \
		$(KRML_HOME)/krmllib/TestLib.ml \
		$(KRML_HOME)/krmllib/C.ml \
		tmp/Crypto_KrmlTest.ml


OBJ_FILES=$(addprefix tmp/, \
	FStar_Mul.o \
	FStar_Squash.o FStar_StrongExcludedMiddle.o FStar_List_Tot_Base.o \
		FStar_Classical.o FStar_List_Tot_Properties.o FStar_List_Tot.o FStar_Seq_Base.o FStar_Seq_Properties.o   FStar_Seq.o \
		FStar_Math_Lemmas.o FStar_BitVector.o \
		FStar_FunctionalExtensionality.o \
		FStar_PropositionalExtensionality.o FStar_PredicateExtensionality.o \
		FStar_TSet.o FStar_Ghost.o \
		FStar_Bytes.o Buffer_Utils.o Crypto_Symmetric_Bytes.o \
		Crypto_Symmetric_Poly1305_Spec.o Crypto_Symmetric_Poly1305_Parameters.o \
		Crypto_Symmetric_Poly1305_Bigint.o Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.o \
		Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.o \
		Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.o \
		Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.o \
		Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.o \
		FStar_Buffer_Quantifiers.o \
		Crypto_Symmetric_AES.o \
		Crypto_Symmetric_AES128.o \
		Crypto_Symmetric_Chacha20.o \
		Crypto_Indexing.o \
		Crypto_Symmetric_Cipher.o \
		Crypto_Symmetric_GF128_Spec.o \
		Crypto_Symmetric_Poly1305_Lemmas.o \
		Flag.o \
		Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part6.o \
		Crypto_Symmetric_Poly1305_Bignum.o \
		Crypto_Symmetric_Poly1305.o \
		Crypto_Symmetric_GF128.o \
		Crypto_Symmetric_MAC.o \
		Crypto_Symmetric_UF1CMA.o \
		Crypto_Plain.o \
		Crypto_Symmetric_PRF.o \
		Crypto_AEAD_Encoding.o \
		Crypto_AEAD_Invariant.o \
		Crypto_AEAD_Lemmas_Part2.o \
		Crypto_AEAD_Lemmas.o \
		Crypto_AEAD.o )

ocaml-test-extract: ulib
	mkdir -p tmp
	$(FSTAR_EXTRACT) --include crypto/hacl/ \
		--include $(KRML_HOME)/krmllib --include $(KRML_HOME)/test/ \
		--odir tmp crypto/Crypto.KrmlTest.fst
	echo "let _ = main()" >> tmp/Crypto_KrmlTest.ml

ocaml-test.exe: ocaml-test-extract
	$(OCAMLOPT) -I tmp -I crypto/ml -I $(AEAD_ODIR) $(OCAML_FILES) -o ocaml-test.exe
	./ocaml-test.exe

OPENSSL_HOME=../../contrib/CoreCrypto/ml/openssl
#OPENSSL_HOME=/usr/local/Cellar/openssl\@1.1/1.1.0c
#CC=gcc-6 

# Cleaning
clean:
	@rm -f $(addprefix crypto/ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) $(AEAD_ODIR) $(AES_ODIR) $(AESGCM_ODIR) $(CHACHA_AEAD_ODIR) tmp karamel *~ *.exe ./crypto/*~
