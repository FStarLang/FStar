FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --warn_error -272 # top-level effects

EXTRACT :=
EXTRACT += --extract 'FStarC'

# We need to extract pervasives since extracted code
# uses its own definitions of options, tuples, either, etc.
EXTRACT += --extract +FStar.Pervasives
EXTRACT += --extract -FStar.Pervasives.Native

ROOTS :=
ROOTS += $(SRC)/fstar/FStarC.Main.fst

include mk/generic-0.mk
