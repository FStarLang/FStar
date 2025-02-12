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

# Extract tuple files, mostly for when we use the projectors directly.
EXTRACT += --extract +FStar.Tuple2
EXTRACT += --extract +FStar.Tuple3
EXTRACT += --extract +FStar.Tuple4
EXTRACT += --extract +FStar.Tuple5
EXTRACT += --extract +FStar.Tuple6
EXTRACT += --extract +FStar.Tuple7
EXTRACT += --extract +FStar.Tuple8
EXTRACT += --extract +FStar.Tuple9
EXTRACT += --extract +FStar.Tuple10
EXTRACT += --extract +FStar.Tuple11
EXTRACT += --extract +FStar.Tuple12
EXTRACT += --extract +FStar.Tuple13
EXTRACT += --extract +FStar.Tuple14
EXTRACT += --extract +FStar.DTuple3
EXTRACT += --extract +FStar.DTuple4
EXTRACT += --extract +FStar.DTuple5

ROOTS :=
ROOTS += $(SRC)/fstar/FStarC.Main.fst

include mk/generic.mk
