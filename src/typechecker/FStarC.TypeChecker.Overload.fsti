(*
   Copyright 2008-2025 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(** Shared machinery for type-based overloading resolution.

    F* resolves a name to a candidate set at desugaring time and then uses type
    information to pick among the candidates while typechecking. This module
    holds the parts of that process that are common to every flavour of it:
    classifying a type by its rigid head symbol, deciding when two such
    classifications are definitely incompatible, decomposing a candidate's type
    into formals, and rendering candidates in diagnostics.

    What is deliberately *not* here is the scoring, i.e. the choice of which
    signal discriminates between candidates. That differs per flavour: record
    literals use the expected type and then the set of field names, record
    patterns use the scrutinee type, projectors use the type of the first
    argument, and ordinary names use arity plus all argument types plus the
    expected type. Each caller supplies its own.

    The overriding invariant is that classification here must
    *over-approximate* compatibility: a candidate may be eliminated only when it
    is definitely ill-typed. A false-positive elimination is the only way
    overloading can reject a program that scope-order name resolution alone
    would have accepted. *)
module FStarC.TypeChecker.Overload

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env

module S = FStarC.Syntax.Syntax

(** The classification of a type for the purposes of overload resolution: the
    head symbol of its unrefined weak-head normal form. *)
type base_typ =
  (** The head is an fvar that weak-head normalization could not unfold: an
      abstract or assumed type, or a type constructor. Compared by head symbol
      only, so [list int] and [list bool] both classify as [Base_rigid list] and
      are indistinguishable. That is intentional: it keeps the test purely
      syntactic and immune to unification variables appearing in the type
      arguments, which is what makes it safe to run speculatively. *)
  | Base_rigid of fv
  (** The head is a universe. The universe itself is deliberately not recorded:
      comparing universes would make universe-polymorphic candidates look
      incompatible when they are not. *)
  | Base_type
  (** A unification variable, a bound or type variable, an unresolved implicit,
      an arrow, or a type we simply could not compute. Never eliminates
      anything. Arrows land here on purpose, since a candidate's formal may be a
      type abbreviation we chose not to unfold. *)
  | Base_unknown

(** Toggle for [--debug Overload]. *)
val dbg : ref bool

instance val showable_base_typ : Class.Show.showable base_typ

(** Classify [t]. Normalizes with [Unascribe; Unmeta; Unrefine], so
    [x:nat{x > 17}] classifies the same as [int], and [eqtype] the same as
    [Type].

    Normalization must not unfold abstract types. [FStar.UInt32.t] is declared
    [new val t : eqtype] and so stays rigid; were it to collapse to [Prims.int],
    an overload of [+] on machine integers would be indistinguishable from the
    one on [int]. *)
val base_of_typ : env -> typ -> ML base_typ

(** [base_of_typ] restricted to the rigid case. This is the signal the record
    and projector paths use: the head type constructor of a type, if there is
    one. *)
val base_head_fv : env -> typ -> ML (option fv)

(** Are these two classifications *possibly* compatible?

    [Base_unknown] is compatible with everything; this is the
    over-approximation that keeps resolution conservative. Two rigid heads are
    compatible exactly when they are the same lident. Note this relation is
    reflexive and symmetric but deliberately *not* transitive, since
    [Base_unknown] relates everything. *)
val compatible : base_typ -> base_typ -> bool

(** Split [t] into its formals and result, normalizing enough to see through
    type abbreviations and [Tot] wrappers. Implicit binders are retained; the
    caller decides how to line them up with explicit arguments. *)
val formals_of_typ : env -> typ -> ML (list binder & comp)

(** The classification of the [i]th *explicit* formal of a function of type [t],
    0-based, or [Base_unknown] if [t] has no such formal (in which case nothing
    can be concluded and nothing may be eliminated). *)
val nth_explicit_formal_base : env -> typ -> int -> ML base_typ

(** Can a function of type [t] be applied to [n] explicit arguments?

    Conservative: returns [true] whenever we cannot tell, e.g. when the result
    after consuming the visible binders is not syntactically an arrow but might
    still reduce to one. Only a candidate that definitely runs out of binders is
    rejected. *)
val arity_compatible : env -> typ -> int -> ML bool

(** Render a candidate set for an error message or a debug trace: each
    candidate's fully qualified name and type, one per line. *)
val candidates_doc : env -> list fv -> ML (list Pprint.document)

(** Pick a candidate for an overloaded name.

    [resolve env speculate primary alts args expected] chooses among
    [primary :: alts], which are given in scope order, innermost binding first.
    [primary] is therefore the candidate that scope-order name resolution
    selects on its own, i.e. the answer when overloading is disabled.

    [speculate] classifies the type of an argument term. It is supplied by the
    caller because this module cannot depend on the typechecker; it is expected
    to typecheck the term speculatively and to return [Base_unknown] rather
    than raising if that fails. It is called at most once per explicit
    argument, and only while more than one candidate is still in play.

    [args] are the *explicit* arguments at the application site, in order;
    [expected] is the expected type of the whole application, if known.

    The algorithm is a sequence of filters -- arity, then each argument
    left to right, then the result type -- and it is conservative in three
    separate ways:

      - a candidate is eliminated only when its formal and the argument have
        two *different rigid heads*, so anything unknown eliminates nothing,
        and "different rigid heads" is weaker than "different types" on
        purpose: the elaborator inserts coercions, so [compatible] treats
        [bool], [prop] and [Type] as mutually possible, and likewise [erased t]
        and [t];
      - if a filter would eliminate *every* remaining candidate it is skipped
        entirely, so we never turn a type error into a resolution error;
      - if several candidates survive, we return the first of *them*, in scope
        order.

    Note that the last point returns the first *surviving* candidate, which is
    [primary] only when [primary] survived every filter. If [primary] was
    eliminated and more than one alternative remains, the answer is an
    alternative. [resolve] thus preserves the scope-order answer exactly when
    the filters do not reject it, and it never revisits a rejection.

    That is why [resolve] is only half of the mechanism. Its answer is no
    better than the head-symbol approximation in [compatible], which cannot see
    coercions, subtyping or typeclass constraints and so can reject a candidate
    that would in fact have typechecked. [TcTerm.resolve_overloaded_head]
    closes that gap: whenever [resolve] answers something other than [primary],
    it re-checks [primary] against the real arguments and expected type and
    keeps [primary] if that succeeds. Only the two together implement the
    intended contract, namely that the scope-order candidate is displaced only
    when it genuinely does not typecheck.

    Under [--ext fstar:overload=strict] a surviving set of more than one
    candidate is reported as [Error_AmbiguousName] instead of being silently
    resolved. The first survivor is still returned, so that a single file
    reports all of its ambiguities rather than stopping at the first, and so
    that [--warn_error] can demote the report and recover the scope-order
    answer. *)
val resolve :
     env
  -> (term -> ML base_typ)
  -> fv
  -> list fv
  -> list term
  -> option typ
  -> ML fv
