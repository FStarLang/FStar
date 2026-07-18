FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --warn_error -272 # top-level effects

# This is a UNIFIED extraction pass: it extracts BOTH the compiler
# (FStarC* + FStar.Pervasives) AND the in-tree ulib plugins (the
# FStar.Tactics.*, FStar.Reflection.*, etc. modules that used to be
# extracted separately by mk/plugins.mk) into a single OUTPUT_DIR.
# It is meant to be run with CODEGEN=PluginNoLib so that the [@@plugin]
# annotations in both the compiler and the plugin modules get their
# registration code emitted.

EXTRACT :=

# --- Compiler ---
EXTRACT += --extract 'FStarC'

# We need to extract pervasives since extracted code
# uses its own definitions of options, tuples, either, etc.
EXTRACT += --extract +FStar.Pervasives
EXTRACT += --extract -FStar.Pervasives.Native

# --- In-tree plugins (folded in from the former mk/plugins.mk pass) ---
# These namespaces, intersected with what is reachable from the plugin
# ROOTS below, yield exactly the module set the plugins pass used to
# produce. Modules not reachable from the roots are not extracted.
EXTRACT += --extract +FStar.Tactics
EXTRACT += --extract +FStar.Reflection
EXTRACT += --extract +FStar.Sealed
EXTRACT += --extract +FStar.Order
EXTRACT += --extract +FStar.BitVector
EXTRACT += --extract +FStar.Seq
EXTRACT += --extract +FStar.Int
EXTRACT += --extract +FStar.UInt
EXTRACT += --extract +FStar.BV
EXTRACT += --extract +FStar.Fin
EXTRACT += --extract +FStar.Calc
EXTRACT += --extract +FStar.Math
EXTRACT += --extract +FStar.Bijection
EXTRACT += --extract +FStar.Injection
EXTRACT += --extract +FStar.Functions
EXTRACT += --extract +FStar.NormSteps
EXTRACT += --extract +FStar.Algebra.CommMonoid.Equiv
EXTRACT += --extract +FStar.Preorder
EXTRACT += --extract +FStar.Monotonic.Pure
EXTRACT += --extract +FStar.List.Tot.Properties
EXTRACT += --extract +FStar.Classical
EXTRACT += --extract +FStar.IndefiniteDescription
EXTRACT += --extract +FStar.Nonempty
EXTRACT += --extract +FStar.PropositionalExtensionality
EXTRACT += --extract +FStar.SizeT

ROOTS :=
ROOTS += $(SRC)/fstar/FStarC.Main.fst

# Plugin roots: the files that define plugins in the library, so we make
# sure to also extract them and link them into F*. (Formerly in mk/plugins.mk.)
ROOTS += ulib/FStar.Tactics.Effect.fsti
ROOTS += ulib/FStar.Order.fst
ROOTS += ulib/FStar.Reflection.TermEq.fsti
ROOTS += ulib/FStar.Reflection.TermEq.Simple.fsti
ROOTS += ulib/FStar.Reflection.V2.Compare.fsti
ROOTS += ulib/FStar.Reflection.V2.Formula.fst
ROOTS += ulib/FStar.Tactics.BV.fsti
ROOTS += ulib/FStar.Tactics.CanonCommMonoidSimple.Equiv.fst
ROOTS += ulib/FStar.Tactics.Canon.fst
ROOTS += ulib/FStar.Tactics.Canon.fsti
ROOTS += ulib/FStar.Tactics.CheckLN.fsti
ROOTS += ulib/FStar.Tactics.Easy.fsti
ROOTS += ulib/FStar.Tactics.MApply0.fsti
ROOTS += ulib/FStar.Tactics.MkProjectors.fsti
ROOTS += ulib/FStar.Tactics.NamedView.fsti
ROOTS += ulib/FStar.Tactics.Names.fsti
ROOTS += ulib/FStar.Tactics.Parametricity.fsti
ROOTS += ulib/FStar.Tactics.Print.fsti
ROOTS += ulib/FStar.Tactics.SMT.fsti
ROOTS += ulib/FStar.Tactics.Typeclasses.fsti
ROOTS += ulib/FStar.Tactics.TypeRepr.fsti
ROOTS += ulib/FStar.Tactics.V2.Logic.fsti
ROOTS += ulib/FStar.Tactics.V2.SyntaxHelpers.fst
ROOTS += ulib/FStar.Tactics.Visit.fst
ROOTS += ulib/FStar.Tactics.PrettifyType.fst
ROOTS += ulib/FStar.Tactics.LaxTermEq.fst

include mk/generic-1.mk
