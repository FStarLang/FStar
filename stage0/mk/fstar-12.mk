FSTAR_OPTIONS += --lax
# HACK ALERT! --MLish passed by generic.mk to FStarC modules
# only. Passing it here would mean the library is checked with
# --MLish, which fails.
FSTAR_OPTIONS += --MLish_effect 'FStarC.Effect'

# FIXME: Maintaining this list sucks. Could **the module** itself
# specify whether it is noextract? Actually, the F* compiler should
# already know which of its modules are in its library, and do this by
# default.
EXTRACT :=
EXTRACT += --extract ',*' # keep the comma (https://github.com/FStarLang/FStar/pull/3640)
EXTRACT += --extract -Prims
EXTRACT += --extract -FStar
EXTRACT += --extract -FStarC.Extraction.ML.PrintML # very much a special case

# Library wrangling
EXTRACT += --extract +FStar.Pervasives
EXTRACT += --extract -FStar.Pervasives.Native
EXTRACT += --extract +FStar.Class.Printable
EXTRACT += --extract +FStar.Seq.Base
EXTRACT += --extract +FStar.Seq.Properties

ROOTS :=
ROOTS += $(SRC)/fstar/FStarC.Main.fst

include mk/generic-1.mk
