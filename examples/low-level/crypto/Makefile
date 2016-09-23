FSTAR_HOME=../../..

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

HINTS_ENABLED?=--use_hints

OPTIONS=--fstar_home $(FSTAR_HOME) --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 20  $(HINTS_ENABLED)

FSTAR_INCLUDE_PATHS=--include $(FSTAR_HOME)/ulib/hyperheap --include $(FSTAR_HOME)/ucontrib/Platform/fst

# Files that should fully typecheck
# Files commented out are broken, uncomment once fixed
VERIFY= \
  FStar.HST.Monotonic.RRef \
  TestMonotonic \
  Buffer.Utils \
  Math.Axioms \
  Math.Lemmas \
  Math.Lib \
  Curve.Bigint \
  Curve.Parameters \
  Crypto.Symmetric.Poly1305.Bigint \
  Crypto.Symmetric.Poly1305.Parameters \
  Crypto.Symmetric.Poly1305.Spec \
  Crypto.Symmetric.Poly1305 \
  Crypto.Symmetric.Chacha20 \
  Crypto.Symmetric.BlockCipher \
  Crypto.Symmetric.GF128 \
  Crypto.Symmetric.GCM \
  Crypto.Symmetric.AES \
  Crypto.AEAD.AES256GCM \
  Plain \
  # Test
  # Curve.Modulo 

# Files not yet fully typechecking
# Please move files that you know fully typecheck to VERIFY
# Files commented out are broken, uncomment once fixed
LAX= \
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
  Crypto.Symmetric.Poly1305.MAC \
  Crypto.Symmetric.Chacha20.PRF \
  Crypto.AEAD.Chacha20Poly1305.Ideal \
  Crypto.AEAD.Chacha20Poly1305 \
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
	$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# Lax verifying one file at a time
%.fst-lax:
	$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) --lax \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst
