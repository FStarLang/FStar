FSTAR_HOME=../../..

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

HINTS_ENABLED?=--use_hints

OPTIONS=--fstar_home $(FSTAR_HOME) --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 20  $(HINTS_ENABLED)

FSTAR_INCLUDE_PATHS=--include $(FSTAR_HOME)/ulib/hyperheap --include $(FSTAR_HOME)/ucontrib/Platform/fst

# Files that should fully typecheck
# Files commented out are broken, uncomment once fixed
VERIFY= \
  Buffer.Utils \
  Math.Axioms \
  Math.Lemmas \
  Curve.Bigint \
  Curve.Parameters \
  Crypto.Symmetric.Chacha20 \
  Crypto.Symmetric.Poly1305.Bigint \
  Crypto.Symmetric.Poly1305.Parameters \
  Crypto.Symmetric.Poly1305.Spec \
  Crypto.Symmetric.Poly1305 \
  Crypto.Symmetric.Bytes \
  Crypto.Symmetric.GF128 \
  Crypto.Symmetric.GCM \
  Crypto.Symmetric.AES \
  Crypto.Symmetric.BlockCipher \
  Crypto.AEAD.AES256GCM \
  Crypto.Symmetric.Poly1305.MAC \
  Crypto.Symmetric.Chacha20.PRF \
  Crypto.AEAD.Chacha20Poly1305 \
  Crypto.AEAD.Chacha20Poly1305.Ideal \
  Plain \
  Test \
  # TestMonotonic \
  # FStar.HST.Monotonic.RRef
  # Test
  # Curve.Modulo 

# Files not yet fully typechecking -- possibly due to timeouts.
# Please move files that you know fully typecheck to VERIFY
# Files commented out are broken, uncomment once fixed
LAX= \
  Math.Lib \
  Math.Definitions \
  Math.Field \
  Math.Curve \
  Curve.AddAndDouble \
  Curve.Bignum \
  Curve.Fsum \
  Curve.FsumWide \
  Curve.Fscalar \
  Curve.Crecip \
  Curve.Point \
  Curve.Ladder \
  Crypto.Symmetric.Poly1305.Bignum \
  # AEAD

all-ver: $(addsuffix .fst-ver, $(VERIFY))

all-lax: $(addsuffix .fst-lax, $(LAX))

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
