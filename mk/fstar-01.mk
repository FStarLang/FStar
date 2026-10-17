FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --warn_error -272 # top-level effects


# The compiler (FStarC.*), the in-tree ulib plugins (FStar.Tactics.*,
# FStar.Reflection.*, ...) and the ulib modules that out-of-tree plugins
# (e.g. Pulse) need are all checked here, and extracted into a single
# OUTPUT_DIR by one whole-program Custard pass (mk/custard-extract.mk).
# The ROOTS below bound what is *checked*; the Custard entry points at the
# end bound what is *emitted*.

ROOTS :=
ROOTS += $(SRC)/fstar/FStarC.Main.fst

# Plugin roots: the files that define plugins in the library, so we make
# sure to also extract them and link them into F*.
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

# The two entrypoint files name the definitions a hand-written realization
# reaches by OCaml name -- the compiler's own in src/custard, and Pulse's,
# because Pulse is built by this repo and loaded into this binary.
CUSTARD_UNIT     := fstarc
CUSTARD_ROOT     := $(SRC)/fstar/FStarC.Main.fst
CUSTARD_ENTRYFILES := src/custard/entrypoints.txt pulse/src/custard-entrypoints.txt
CUSTARD_DEPS     := $(CUSTARD_ENTRYFILES)

CUSTARD_ENTRIES := --custard_entry FStarC.Main.main
CUSTARD_ENTRIES += $(patsubst %,--custard_entrypoints %,$(CUSTARD_ENTRYFILES))

include mk/generic-0.mk
