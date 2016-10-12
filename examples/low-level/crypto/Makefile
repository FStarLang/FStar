FSTAR_HOME=../../..

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

HINTS_ENABLED?=--use_hints

OPTIONS=--fstar_home $(FSTAR_HOME) --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 20  $(HINTS_ENABLED) $(OTHERFLAGS)

FSTAR_INCLUDE_PATHS=--include $(FSTAR_HOME)/ulib/hyperheap --include $(FSTAR_HOME)/ucontrib/Platform/fst

# Files that should fully typecheck
# Files commented out are broken, uncomment once fixed
VERIFY= \
  FStar.HST.Monotonic.RRef \
  Buffer.Utils \
  Crypto.Symmetric.Chacha20 \
  Crypto.Symmetric.Poly1305.Bigint \
  Crypto.Symmetric.Poly1305.Parameters \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1 \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2 \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3 \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4 \
  Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part5 \
  Crypto.Symmetric.Poly1305.Bignum \
  Crypto.Symmetric.Poly1305.Spec \
  Crypto.Symmetric.Poly1305 \
  Crypto.Symmetric.Bytes \
  Crypto.Symmetric.GF128 \
  Crypto.Symmetric.GCM \
  Crypto.Symmetric.AES \
  Crypto.Symmetric.Cipher \
  Crypto.AEAD.AES256GCM \
  Crypto.Symmetric.PRF \
  Crypto.AEAD.Chacha20Poly1305 \
  Crypto.AEAD \
  Plain \
  Test \
  TestMonotonic

# Files that should fully typecheck, but not part of regression
# because verification is too slow
SLOW= \

# Files not yet fully typechecking -- possibly due to timeouts.
# Please move files that you know fully typecheck to VERIFY
# Files commented out are broken, uncomment once fixed
LAX= \
  Crypto.Symmetric.Poly1305.MAC

#16-10-09  Not sure how to verify Flag.fsti and Flag.fst

all-ver: $(addsuffix .fst-ver, $(VERIFY))

all-lax: $(addsuffix .fst-lax, $(LAX)) $(addsuffix .fst-lax, $(VERIFY))

# Parameter for interactive mode
%.fst-in: 
	@echo $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--verify_module $(basename $(notdir $@))

# Verifying one file at a time
%.fst-ver:
	-$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# Lax verifying one file at a time
%.fst-lax:
	$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) --lax \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst
