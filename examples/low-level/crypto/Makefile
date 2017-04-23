FSTAR_HOME=../../..

FSTAR?=$(FSTAR_HOME)/bin/fstar.exe

HINTS_ENABLED?=--use_hints

OPTIONS=--fstar_home $(FSTAR_HOME) --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 0 --z3rlimit 20  $(HINTS_ENABLED) $(OTHERFLAGS)

FSTAR_INCLUDE_PATHS=--include $(FSTAR_HOME)/ulib/hyperstack --include hacl

# Files that should fully typecheck
# Files commented out are broken, uncomment once fixed
VERIFY= \
  Buffer.Utils \
  Crypto.Symmetric.Bytes \
  Crypto.Symmetric.Poly1305.Bigint \
  Crypto.Symmetric.Poly1305.Parameters \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1 \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2 \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3 \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4 \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part5 \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part6 \
  Crypto.Symmetric.Poly1305.Bignum \
  Crypto.Symmetric.Poly1305.Spec \
  Crypto.Symmetric.GF128 \
  Crypto.Symmetric.GCM \
  Crypto.Symmetric.MAC \
  Crypto.Symmetric.UF1CMA \
  Crypto.Symmetric.AES \
  Crypto.Symmetric.AES128 \
  Crypto.Symmetric.Chacha20 \
  Crypto.Symmetric.Cipher \
  Crypto.Symmetric.PRF \
  Crypto.AEAD.AES256GCM \
  Crypto.AEAD.Encoding \
  Crypto.AEAD.Invariant \
  Crypto.AEAD.BufferUtils \
  Crypto.AEAD.Encrypt.Invariant \
  Crypto.AEAD.Enxor.Invariant \
  Crypto.AEAD.EnxorDexor \
  Crypto.AEAD.Wrappers.PRF \
  Crypto.AEAD.Wrappers.CMA \
  Crypto.AEAD.Wrappers.Encoding \
  Crypto.AEAD.Decrypt \
  Crypto.AEAD.MAC_Wrapper.Invariant \
  Crypto.AEAD.Encrypt.Ideal.Invariant \
  Crypto.AEAD.Encrypt \
  Crypto.AEAD \
  Crypto.Plain \
  TestMonotonic

EXTRA= \
  Crypto.Symmetric.Poly1305 \
  Crypto.Test

#  Crypto.Symmetric.Poly1305.Lemmas  # verification target is not passing reliably so commenting out

#16-10-30 removed files specific to Poly1305:
#  Crypto.Symmetric.Poly1305.MAC 
#  Crypto.AEAD.Chacha20Poly1305


# Files that should fully typecheck, but not part of regression
# because verification is too slow
SLOW= \

# Files not yet fully typechecking -- possibly due to timeouts.
# Please move files that you know fully typecheck to VERIFY
# Files commented out are broken, uncomment once fixed
LAX=

# \
#   Crypto.Symmetric.Poly1305 \
#   Crypto.AEAD #NS: both of these verify, but each takes 20+ mins to verify


#16-10-09  Not sure how to verify Flag.fsti and Flag.fst

all: all-ver $(addsuffix .fst-lax, $(LAX))

extra: all-ver $(addsuffix .fst-ver, $(EXTRA))

all-ver: $(addsuffix .fst-ver, $(VERIFY))

all-lax: $(addsuffix .fst-lax, $(LAX)) $(addsuffix .fst-lax, $(VERIFY))

# Parameter for interactive mode
%.fst-in: 
	@echo $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--__temp_no_proj Crypto.Symmetric.MAC \
	--verify_module $(basename $(notdir $@))

# Verifying one file at a time
%.fst-ver:
	$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--__temp_no_proj Crypto.Symmetric.MAC \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# Lax verifying one file at a time
%.fst-lax:
	$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) --lax \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

AEAD_FILES=$(addsuffix .fst, $(VERIFY))
aead-ver: $(addsuffix -ver, $(AEAD_FILES))

aead-wc:
	wc -l $(AEAD_FILES)

all-assumes: $(addsuffix .fst, $(VERIFY) $(LAX))
	grep "\(assume\)\|\(admit\)\|\(lax\)" $^


include $(FSTAR_HOME)/src/gmake/fstar.mk
CFSTAR=$(subst CURRENT_DIR,examples/low-level/crypto,$(CVERFSTAR))
all-cver: $(addsuffix .fst-cver, $(VERIFY)) 
%.fst-cver: CVERCONFIG
	$(CFSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--__temp_no_proj Crypto.Symmetric.MAC \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst
