FSTAR_OPTIONS += --lax
# HACK ALERT! --MLish passed by generic.mk to FStarC modules
# only. Passing it here would mean the library is checked with
# --MLish, which fails.
FSTAR_OPTIONS += --MLish_effect 'FStarC.Effect'

EXTRACT :=
EXTRACT += --extract 'FStarC'

# We need to extract pervasives since extracted code
# uses its own definitions of options, tuples, either, etc.
EXTRACT += --extract +FStar.Pervasives
EXTRACT += --extract -FStar.Pervasives.Native

ROOTS :=
ROOTS += $(SRC)/fstar/FStarC.Main.fst

include mk/generic-1.mk
