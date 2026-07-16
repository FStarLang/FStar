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

# --- Out-of-tree plugin base modules (formerly the fstar_pluginlib /
# fstar.compiler.plugins library, extracted from ulib.pluginml). These are
# the ulib plugin-usable modules that out-of-tree plugins (e.g. Pulse) need
# but the compiler does not itself reach. Folding them into fstarcompiler
# eliminates the separate fstar_pluginlib library/namespace.
EXTRACT += --extract +FStar.Algebra.CommMonoid
EXTRACT += --extract +FStar.Algebra.CommMonoid.Fold
EXTRACT += --extract +FStar.Algebra.CommMonoid.Fold.Nested
EXTRACT += --extract +FStar.Algebra.Monoid
EXTRACT += --extract +FStar.BigOps
EXTRACT += --extract +FStar.Cardinality.Cantor
EXTRACT += --extract +FStar.Cardinality.Universes
EXTRACT += --extract +FStar.Class.Add
EXTRACT += --extract +FStar.Class.Eq
EXTRACT += --extract +FStar.Class.Eq.Raw
EXTRACT += --extract +FStar.Class.Ord.Raw
EXTRACT += --extract +FStar.Class.Printable
EXTRACT += --extract +FStar.Class.TotalOrder.Raw
EXTRACT += --extract +FStar.ConstantTime.Integers
EXTRACT += --extract +FStar.DependentMap
EXTRACT += --extract +FStar.Endianness
EXTRACT += --extract +FStar.Enumerable
EXTRACT += --extract +FStar.Error
EXTRACT += --extract +FStar.ExtractAs
EXTRACT += --extract +FStar.FiniteMap.Ambient
EXTRACT += --extract +FStar.FiniteMap.Base
EXTRACT += --extract +FStar.FiniteSet.Ambient
EXTRACT += --extract +FStar.FiniteSet.Base
EXTRACT += --extract +FStar.FunctionalExtensionality
EXTRACT += --extract +FStar.FunctionalQueue
EXTRACT += --extract +FStar.GSet
EXTRACT += --extract +FStar.GhostSet
EXTRACT += --extract +FStar.IFC
EXTRACT += --extract +FStar.Int128
EXTRACT += --extract +FStar.Int.Cast.Full
EXTRACT += --extract +FStar.IntegerIntervals
EXTRACT += --extract +FStar.Integers
EXTRACT += --extract +FStar.LexicographicOrdering
EXTRACT += --extract +FStar.List.Pure.Base
EXTRACT += --extract +FStar.Map
EXTRACT += --extract +FStar.MarkovsPrinciple
EXTRACT += --extract +FStar.Math.Euclid
EXTRACT += --extract +FStar.Math.Exp
EXTRACT += --extract +FStar.Math.Fermat
EXTRACT += --extract +FStar.Matrix
EXTRACT += --extract +FStar.OrdMap
EXTRACT += --extract +FStar.OrdMapProps
EXTRACT += --extract +FStar.OrdSet
EXTRACT += --extract +FStar.OrdSetProps
EXTRACT += --extract +FStar.PCM
EXTRACT += --extract +FStar.PartialMap
EXTRACT += --extract +FStar.PredicateExtensionality
EXTRACT += --extract +FStar.PtrdiffT
EXTRACT += --extract +FStar.Pure.BreakVC
EXTRACT += --extract +FStar.RBMap
EXTRACT += --extract +FStar.RBSet
EXTRACT += --extract +FStar.RefinementExtensionality
EXTRACT += --extract +FStar.Reflection
EXTRACT += --extract +FStar.Reflection.Formula
EXTRACT += --extract +FStar.Reflection.Typing
EXTRACT += --extract +FStar.ReflexiveTransitiveClosure
EXTRACT += --extract +FStar.Seq.Equiv
EXTRACT += --extract +FStar.Seq.Permutation
EXTRACT += --extract +FStar.Seq.Sorted
EXTRACT += --extract +FStar.Sequence
EXTRACT += --extract +FStar.Sequence.Ambient
EXTRACT += --extract +FStar.Sequence.Base
EXTRACT += --extract +FStar.Sequence.Permutation
EXTRACT += --extract +FStar.Sequence.Seq
EXTRACT += --extract +FStar.Sequence.Util
EXTRACT += --extract +FStar.Set
EXTRACT += --extract +FStar.Tactics.Arith
EXTRACT += --extract +FStar.Tactics.BreakVC
EXTRACT += --extract +FStar.Tactics.CanonCommMonoid
EXTRACT += --extract +FStar.Tactics.CanonCommMonoidSimple
EXTRACT += --extract +FStar.Tactics.CanonCommSemiring
EXTRACT += --extract +FStar.Tactics.CanonMonoid
EXTRACT += --extract +FStar.Tactics.Derived
EXTRACT += --extract +FStar.Tactics.Logic
EXTRACT += --extract +FStar.Tactics.PatternMatching
EXTRACT += --extract +FStar.Tactics.Simplifier
EXTRACT += --extract +FStar.Tactics.SyntaxHelpers
EXTRACT += --extract +FStar.UInt128
EXTRACT += --extract +FStar.Universe
EXTRACT += --extract +FStar.Universe.PCM
EXTRACT += --extract +FStar.WellFounded
EXTRACT += --extract +FStar.WellFoundedRelation
EXTRACT += --extract +FStar.WellFounded.Util

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

# Roots for the folded-in out-of-tree plugin base modules (see above).
ROOTS += ulib/FStar.Algebra.CommMonoid.fst
ROOTS += ulib/FStar.Algebra.CommMonoid.Fold.fst
ROOTS += ulib/FStar.Algebra.CommMonoid.Fold.Nested.fst
ROOTS += ulib/FStar.Algebra.Monoid.fst
ROOTS += ulib/FStar.BigOps.fst
ROOTS += ulib/FStar.Cardinality.Cantor.fst
ROOTS += ulib/FStar.Cardinality.Universes.fst
ROOTS += ulib/FStar.Class.Add.fst
ROOTS += ulib/FStar.Class.Eq.fst
ROOTS += ulib/FStar.Class.Eq.Raw.fst
ROOTS += ulib/FStar.Class.Ord.Raw.fst
ROOTS += ulib/FStar.Class.Printable.fst
ROOTS += ulib/FStar.Class.TotalOrder.Raw.fst
ROOTS += ulib/FStar.DependentMap.fst
ROOTS += ulib/FStar.Endianness.fst
ROOTS += ulib/FStar.Enumerable.fst
ROOTS += ulib/FStar.Error.fst
ROOTS += ulib/FStar.ExtractAs.fst
ROOTS += ulib/FStar.FiniteMap.Ambient.fst
ROOTS += ulib/FStar.FiniteMap.Base.fst
ROOTS += ulib/FStar.FiniteSet.Ambient.fst
ROOTS += ulib/FStar.FiniteSet.Base.fst
ROOTS += ulib/FStar.FunctionalExtensionality.fst
ROOTS += ulib/FStar.FunctionalQueue.fst
ROOTS += ulib/FStar.GSet.fst
ROOTS += ulib/FStar.GhostSet.fst
ROOTS += ulib/FStar.IFC.fst
ROOTS += ulib/FStar.Int128.fst
ROOTS += ulib/FStar.Int.Cast.Full.fst
ROOTS += ulib/FStar.IntegerIntervals.fst
ROOTS += ulib/FStar.Integers.fst
ROOTS += ulib/FStar.LexicographicOrdering.fst
ROOTS += ulib/FStar.List.Pure.Base.fst
ROOTS += ulib/FStar.Map.fst
ROOTS += ulib/FStar.MarkovsPrinciple.fst
ROOTS += ulib/FStar.Math.Euclid.fst
ROOTS += ulib/FStar.Math.Exp.fst
ROOTS += ulib/FStar.Math.Fermat.fst
ROOTS += ulib/FStar.Matrix.fst
ROOTS += ulib/FStar.OrdMap.fst
ROOTS += ulib/FStar.OrdMapProps.fst
ROOTS += ulib/FStar.OrdSet.fst
ROOTS += ulib/FStar.OrdSetProps.fst
ROOTS += ulib/FStar.PCM.fst
ROOTS += ulib/FStar.PartialMap.fst
ROOTS += ulib/FStar.PredicateExtensionality.fst
ROOTS += ulib/FStar.PtrdiffT.fst
ROOTS += ulib/FStar.Pure.BreakVC.fst
ROOTS += ulib/FStar.RBMap.fst
ROOTS += ulib/FStar.RBSet.fst
ROOTS += ulib/FStar.RefinementExtensionality.fst
ROOTS += ulib/FStar.Reflection.fst
ROOTS += ulib/FStar.Reflection.Formula.fst
ROOTS += ulib/FStar.ReflexiveTransitiveClosure.fst
ROOTS += ulib/FStar.Seq.Equiv.fst
ROOTS += ulib/FStar.Seq.Permutation.fst
ROOTS += ulib/FStar.Seq.Sorted.fst
ROOTS += ulib/FStar.Sequence.fst
ROOTS += ulib/FStar.Sequence.Ambient.fst
ROOTS += ulib/FStar.Sequence.Base.fst
ROOTS += ulib/FStar.Sequence.Permutation.fst
ROOTS += ulib/FStar.Sequence.Seq.fst
ROOTS += ulib/FStar.Sequence.Util.fst
ROOTS += ulib/FStar.Set.fst
ROOTS += ulib/FStar.Tactics.Arith.fst
ROOTS += ulib/FStar.Tactics.BreakVC.fst
ROOTS += ulib/FStar.Tactics.CanonCommMonoid.fst
ROOTS += ulib/FStar.Tactics.CanonCommMonoidSimple.fst
ROOTS += ulib/FStar.Tactics.CanonCommSemiring.fst
ROOTS += ulib/FStar.Tactics.CanonMonoid.fst
ROOTS += ulib/FStar.Tactics.Derived.fst
ROOTS += ulib/FStar.Tactics.Logic.fst
ROOTS += ulib/FStar.Tactics.PatternMatching.fst
ROOTS += ulib/FStar.Tactics.Simplifier.fst
ROOTS += ulib/FStar.Tactics.SyntaxHelpers.fst
ROOTS += ulib/FStar.UInt128.fst
ROOTS += ulib/FStar.Universe.fst
ROOTS += ulib/FStar.Universe.PCM.fst
ROOTS += ulib/FStar.WellFounded.fst
ROOTS += ulib/FStar.WellFoundedRelation.fst
ROOTS += ulib/FStar.WellFounded.Util.fst
ROOTS += ulib/experimental/FStar.Reflection.Typing.fst
ROOTS += ulib/experimental/FStar.ConstantTime.Integers.fst

include mk/generic-0.mk
