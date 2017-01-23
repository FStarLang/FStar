FSTAR_HOME=../..

# using the hyperstack memory model, ulib/ml/Makefile.include used this variable to use appropriate ST files
MEM=HST

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)
CODEGEN_ARGS=--lax --codegen OCaml --no_location_info $(FSTAR_DEFAULT_ARGS)

KREMLIN_HOME=../../../kremlin
KREMLIN=$(KREMLIN_HOME)/Kremlin.native
KREMLIN_ARGS=-tmpdir kremlin -verbose -cc clang -ccopt -Wno-error=pointer-sign -ccopt -Wno-error=non-literal-null-conversion

CHACHA_ODIR=chacha
POLY_ODIR=poly
AEAD_ODIR=aead

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10

FSTAR_EXTRACT=$(FSTAR) $(CODEGEN_ARGS) --include $(FSTAR_HOME)/ulib/hyperstack --include crypto --include crypto/real

CHACHA_EXTRACTED=Buffer_Utils.ml Crypto_Symmetric_Chacha20.ml
POLY_EXTRACTED=FStar_List_Tot.ml FStar_Ghost.ml FStar_Seq.ml FStar_SeqProperties.ml Buffer_Utils.ml Crypto_Config.ml Crypto_Indexing.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part6.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305_Spec.ml Flag.ml Crypto_Symmetric_Poly1305.ml
AEAD_EXTRACTED=FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml Buffer_Utils.ml  Crypto_Config.ml Crypto_Indexing.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Chacha20.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_AES128.ml Crypto_Symmetric_Cipher.ml FStar_Ghost.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part6.ml Crypto_Symmetric_Poly1305_Bignum.ml Flag.ml Crypto_Symmetric_Poly1305_Lemmas.ml Crypto_Symmetric_Poly1305.ml FStar_Monotonic_RRef.ml Crypto_Symmetric_Poly1305_MAC.ml Crypto_AEAD_Chacha20Poly1305.ml
# TODO: remove FStar_BitVector below once it's no longer needed
CHACHA_AEAD_EXTRACTED=Spartan.ml FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml FStar_BitVector.ml FStar_UInt.ml Buffer_Utils.ml Crypto_Config.ml Crypto_Indexing.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_Chacha20.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_AES128.ml Crypto_Symmetric_Cipher.ml FStar_Ghost.ml Flag.ml Crypto_Plain.ml Crypto_Symmetric_GF128_Spec.ml Crypto_Symmetric_GF128.ml Crypto_Symmetric_Poly1305_Spec.ml Crypto_Symmetric_Poly1305_Parameters.ml Crypto_Symmetric_Poly1305_Bigint.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part6.ml Crypto_Symmetric_Poly1305_Bignum.ml Crypto_Symmetric_Poly1305_Lemmas.ml Crypto_Symmetric_Poly1305.ml FStar_Monotonic_RRef.ml Crypto_Symmetric_MAC.ml Crypto_Symmetric_UF1CMA.ml Crypto_Symmetric_PRF.ml Crypto_AEAD_Encoding.ml Crypto_AEAD_Invariant.ml Crypto_AEAD_Encrypt_Invariant.ml Crypto_AEAD_Wrappers_PRF.ml Crypto_AEAD_Wrappers_Encoding.ml Crypto_AEAD_Wrappers_CMA.ml Crypto_AEAD_BufferUtils.ml Crypto_AEAD_Enxor_Invariant.ml Crypto_AEAD_EnxorDexor.ml Crypto_AEAD_MAC_Wrapper_Invariant.ml Crypto_AEAD_Encrypt_Ideal_Invariant.ml Crypto_AEAD_Encrypt.ml Crypto_AEAD_Decrypt.ml Crypto_AEAD.ml

.PHONY: lib-ver chacha-ver chacha-ml ulib

#NS: 12/21, we decided to only check verification on each commit; a full test happens nightly using the extra target
uall:
	+make -C crypto all

extra:
	make clean
	+make chacha-test aes-test aesgcm-test chacha-aead-test
	+make -C crypto all extra
# removed tests poly-test and aead-test, relying on older code.

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

chacha-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Chacha20.fst -skip-compilation

chacha-kremlin-test:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.Symmetric.Chacha20.fst $(addprefix $(KREMLIN_HOME)/test/, main-Chacha.c ../kremlib/testlib.c) -o test_chacha.exe
	./test_chacha.exe

poly-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/real/Flag.fst crypto/Crypto.Symmetric.Poly1305.fst -skip-compilation

poly-kremlin-test:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/real/Flag.fst crypto/Crypto.Symmetric.Poly1305.fst $(addprefix $(KREMLIN_HOME)/test/, main-Poly1305.c ../kremlib/testlib.c) -o test_poly.exe
	./test_poly.exe

aead-kremlin-extract:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst -skip-compilation

aead-kremlin-test:
	mkdir -p kremlin
	$(KREMLIN) $(KREMLIN_ARGS) -I crypto crypto/Crypto.AEAD.Chacha20Poly1305.fst $(addprefix $(KREMLIN_HOME)/test/, main-Aead.c ../kremlib/testlib.c) -o test_aead.exe
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
AESGCM_EXTRACTED=FStar_List_Tot.ml FStar_Ghost.ml FStar_Seq.ml FStar_SeqProperties.ml Buffer_Utils.ml Crypto_Config.ml Crypto_Indexing.ml Crypto_Symmetric_Bytes.ml Crypto_Symmetric_AES.ml Crypto_Symmetric_GF128_Spec.ml Crypto_Symmetric_GF128.ml Crypto_Symmetric_GCM.ml Crypto_AEAD_AES256GCM.ml

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
	$(FSTAR_EXTRACT) --include crypto/hacl/ crypto/Crypto.Test.fst --odir $(CHACHA_AEAD_ODIR) --__temp_no_proj Crypto.Symmetric.MAC
#	@sed -i.bak 's/^let mod.*/ /g' $(CHACHA_AEAD_ODIR)/FStar_UInt.ml ##HACK!--need to fix #310

chacha-aead-compile: chacha-aead-extract
	$(OCAMLOPT) -I crypto/ml -I $(CHACHA_AEAD_ODIR) \
	  $(addprefix $(CHACHA_AEAD_ODIR)/,$(CHACHA_AEAD_EXTRACTED)) \
	  $(CHACHA_AEAD_ODIR)/Crypto_Test.ml -o test_chacha_aead.exe

chacha-aead-test: chacha-aead-compile
	./test_chacha_aead.exe

bignum-ver:
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part5.fst --include crypto
	$(FSTAR) --use_hints crypto/Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part6.fst --include crypto
	$(FSTAR) --use_hints --include crypto crypto/Crypto.Symmetric.Poly1305.Bignum.fst

KRML_INCLUDES=$(addprefix -I ,spartan_aes crypto $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/test)
KRML_ARGS=-verbose -ccopt -maes -ccopt -Wno-error=pointer-sign $(KOPTS)
KRML=$(KREMLIN_HOME)/krml $(KRML_ARGS) $(KRML_INCLUDES) 

spartan_aes/aes.o:
	make -C spartan_aes

extract-krml-test:
	$(FSTAR) --no_extract FStar.Math.Lib --no_extract FStar.HyperHeap --no_extract FStar.HyperStack --no_extract FStar.ST --no_extract FStar.Seq --no_extract FStar.UInt128 --no_extract FStar.Int128 --no_extract FStar.UInt64 --no_extract FStar.Int64 --no_extract FStar.UInt63 --no_extract FStar.Int63 --no_extract FStar.UInt32 --no_extract FStar.Int32 --no_extract FStar.UInt31 --no_extract FStar.Int31 --no_extract FStar.UInt16 --no_extract FStar.Int16 --no_extract FStar.UInt8 --no_extract FStar.Int8 --no_extract Crypto.AEAD.MAC_Wrapper.Invariant --trace_error --include D:/workspace/clean/FStar/ulib/hyperstack --include spartan_aes --include crypto --include ../../../../everest/kremlin/kremlib --include ../../../../everest/kremlin/test --include D:/workspace/everest/kremlin/kremlib crypto/spartan/Crypto.Config.fst crypto/real/Flag.fst crypto/Crypto.KrmlTest.fst

krml-test.exe: spartan_aes/aes.o crypto/*.fst
	$(KRML) crypto/spartan/Crypto.Config.fst crypto/real/Flag.fst \
		spartan_aes/aes.o crypto/spartan_stub.c \
	       	crypto/Crypto.KrmlTest.fst -no-prefix Crypto.KrmlTest \
	       	$(KREMLIN_HOME)/test/../kremlib/testlib.c crypto/test_hacks.c \
		-tmpdir tmp -add-include '"testlib.h"' -o krml-test.exe
	./krml-test.exe

OCAML_FILES=tmp/FStar_Squash.ml tmp/FStar_StrongExcludedMiddle.ml tmp/FStar_List_Tot.ml \
		tmp/FStar_Seq.ml \
		tmp/FStar_Classical.ml tmp/FStar_ListProperties.ml tmp/FStar_SeqProperties.ml \
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
		$(KREMLIN_HOME)/kremlib/TestLib.ml \
		$(KREMLIN_HOME)/kremlib/C.ml \
		tmp/Crypto_KrmlTest.ml


OBJ_FILES=$(addprefix tmp/, \
	FStar_Mul.o \
	FStar_Squash.o FStar_StrongExcludedMiddle.o FStar_List_Tot.o \
		FStar_Classical.o FStar_ListProperties.o FStar_SeqProperties.o \
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
		--include $(KREMLIN_HOME)/kremlib --include $(KREMLIN_HOME)/test/ \
		--odir tmp crypto/Crypto.KrmlTest.fst
	echo "let _ = main()" >> tmp/Crypto_KrmlTest.ml

ocaml-test.exe: ocaml-test-extract
	$(OCAMLOPT) -I tmp -I crypto/ml -I $(AEAD_ODIR) $(OCAML_FILES) -o ocaml-test.exe
	./ocaml-test.exe

OPENSSL_HOME=../../ucontrib/CoreCrypto/ml/openssl
#OPENSSL_HOME=/usr/local/Cellar/openssl\@1.1/1.1.0c
#CC=gcc-6 

test-perf.exe: krml-test.exe crypto/test_perf.c
	$(CC) -Ofast -m64 -march=native -mtune=native -flto -funroll-loops -fomit-frame-pointer \
	 -o test-perf.exe tmp/FStar.c tmp/Crypto_AEAD*.c tmp/Crypto_Symmetric*.c tmp/Crypto_Indexing*.c tmp/Buffer_Utils*.c tmp/Crypto_Plain*.c $(KREMLIN_HOME)/kremlib/kremlib.c \
		$(KREMLIN_HOME)/kremlib/testlib.c crypto/test_perf.c crypto/spartan_stub.c spartan_aes/*.o crypto/test_hacks.c -I tmp -L tmp \
		-I $(KREMLIN_HOME)/kremlib -I $(KREMLIN_HOME)/test \
		-I $(OPENSSL_HOME)/include -L $(OPENSSL_HOME)/lib -L $(OPENSSL_HOME) -lcrypto $(CFLAGS)
	PATH=$(OPENSSL_HOME):"$(PATH)" \
	  LD_LIBRARY_PATH=$(OPENSSL_HOME):"$(LD_LIBRARY_PATH)" \
	  DYLD_LIBRARY_PATH=$(OPENSSL_HOME):"$(DYLD_LIBRARY_PATH)" ./test-perf.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix crypto/ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) $(AEAD_ODIR) $(AES_ODIR) $(AESGCM_ODIR) $(CHACHA_AEAD_ODIR) tmp kremlin *~ *.exe ./crypto/*~
