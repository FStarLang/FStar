include mk/common.mk

$(call need_exe, FSTAR_EXE, fstar.exe to be used)
$(call need, CACHE_DIR, directory for checked files)
$(call need, OUTPUT_DIR, directory for extracted OCaml files)
$(call need, CODEGEN, backend (OCaml / Plugin))
$(call need, SRC, source directory)
$(call need, TAG, a tag for the .depend; to prevent clashes. Sorry.)

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR)
	rm -rf $(OUTPUT_DIR)

.PHONY: ocaml
ocaml: all-ml

FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --cache_checked_modules
FSTAR_OPTIONS += --cache_dir "$(CACHE_DIR)"
FSTAR_OPTIONS += --odir "$(OUTPUT_DIR)"

FSTAR_OPTIONS += --no_default_includes
FSTAR_OPTIONS += --include $(SRC)

FSTAR_OPTIONS += $(OTHERFLAGS)

FSTAR = $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

# FIXME: Maintaining this list sucks. Could **the module** itself specify whether it is
# noextract? Or maybe if we find an aptly-named .ml file then we auto skip?
EXTRACT :=
EXTRACT += --extract '*'
EXTRACT += --extract -Prims
EXTRACT += --extract -FStar.Pervasives.Native
EXTRACT += --extract -FStar.All
EXTRACT += --extract -FStar.Ghost
EXTRACT += --extract -FStar.Heap
EXTRACT += --extract -FStar.Bytes
EXTRACT += --extract -FStar.Char
EXTRACT += --extract -FStar.Exn
EXTRACT += --extract -FStar.Float
EXTRACT += --extract -FStar.Int16
EXTRACT += --extract -FStar.Int32
EXTRACT += --extract -FStar.Int64
EXTRACT += --extract -FStar.Int8
EXTRACT += --extract +FStar.Int.Cast.Full
EXTRACT += --extract -FStar.List
EXTRACT += --extract +FStar.List.Pure.Base
EXTRACT += --extract +FStar.List.Tot.Properties
EXTRACT += --extract -FStar.Monotonic.Heap
EXTRACT += --extract -FStar.HyperStack.ST
EXTRACT += --extract -FStar.Option
EXTRACT += --extract -FStar.Printf
EXTRACT += --extract -FStar.Range
EXTRACT += --extract -FStar.ST
EXTRACT += --extract -FStar.String
EXTRACT += --extract -FStar.TSet
EXTRACT += --extract -FStar.UInt16
EXTRACT += --extract -FStar.UInt32
EXTRACT += --extract -FStar.UInt64
EXTRACT += --extract -FStar.UInt8
EXTRACT += --extract -FStar.Util
  
# EXTRACT += --extract -FStar.BitVector
# EXTRACT += --extract -FStar.Calc

%.checked.lax:
	$(call msg, "LAXCHECK", $(basename $(basename $(notdir $@))))
	$(FSTAR) $(if $(findstring /ulib/,$<),,--MLish) $<
	@touch -c $@  ## SHOULD NOT BE NEEDED

%.ml: FF=$(notdir $(subst .checked.lax,,$<))
%.ml: MM=$(basename $(FF))
%.ml:
	$(call msg, "EXTRACT", $(notdir $@))
	@# HACK we use notdir to get the module name since we need to pass in the
	@# fst (not the checked file), but we don't know where it is, so this is
	@# relying on F* looking in its include path. sigh.
	$(FSTAR) $(FF) \
	  --codegen $(CODEGEN) \
	  --extract_module $(MM)
	@touch -c $@  ## SHOULD NOT BE NEEDED

# --------------------------------------------------------------------
# Dependency analysis for bootstrapping
# --------------------------------------------------------------------

# List here the files that define plugins in the library,
# so we make sure to also extract them and link them into F*.
# MUST BE NON EMPTY OR WE WILL EXTRACT THE ENTIRE LIBRARY
ROOTS += ../ulib/FStar.Tactics.Effect.fsti
ROOTS += ../ulib/FStar.Order.fst
ROOTS += ../ulib/FStar.Reflection.TermEq.fsti
ROOTS += ../ulib/FStar.Reflection.TermEq.Simple.fsti
ROOTS += ../ulib/FStar.Reflection.V2.Compare.fsti
ROOTS += ../ulib/FStar.Reflection.V2.Formula.fst
ROOTS += ../ulib/FStar.Tactics.BV.fsti
ROOTS += ../ulib/FStar.Tactics.CanonCommMonoidSimple.Equiv.fst
ROOTS += ../ulib/FStar.Tactics.Canon.fst
ROOTS += ../ulib/FStar.Tactics.Canon.fsti
ROOTS += ../ulib/FStar.Tactics.CheckLN.fsti
ROOTS += ../ulib/FStar.Tactics.MApply0.fsti
ROOTS += ../ulib/FStar.Tactics.MkProjectors.fsti
ROOTS += ../ulib/FStar.Tactics.NamedView.fsti
ROOTS += ../ulib/FStar.Tactics.Names.fsti
ROOTS += ../ulib/FStar.Tactics.Parametricity.fsti
ROOTS += ../ulib/FStar.Tactics.Print.fsti
ROOTS += ../ulib/FStar.Tactics.SMT.fsti
ROOTS += ../ulib/FStar.Tactics.Typeclasses.fsti
ROOTS += ../ulib/FStar.Tactics.TypeRepr.fsti
ROOTS += ../ulib/FStar.Tactics.V1.Logic.fsti
ROOTS += ../ulib/FStar.Tactics.V2.Logic.fsti
ROOTS += ../ulib/FStar.Tactics.V2.SyntaxHelpers.fst
ROOTS += ../ulib/FStar.Tactics.Visit.fst

$(CACHE_DIR)/.depend$(TAG):
	$(call msg, "DEPEND")
	$(FSTAR) --dep full $(ROOTS) $(EXTRACT) --output_deps_to $@
	mkdir -p $(CACHE_DIR)

depend: $(CACHE_DIR)/.depend$(TAG)
include $(CACHE_DIR)/.depend$(TAG)

all-ml: $(ALL_ML_FILES)
