(*
   Copyright 2008-2018 Microsoft Research

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

module FStar.FunctionalExtensionality

/// Functional extensionality asserts the equality of pointwise-equal
/// functions.
///
/// The formulation of this axiom is particularly subtle in F* because
/// of its interaction with subtyping. In fact, prior formulations of
/// this axiom were discovered to be unsound by Aseem Rastogi.
///
/// The predicate [feq #a #b f g] asserts that [f, g: x:a -> (b x)] are
/// pointwise equal on the domain [a].
///
/// However, due to subtyping [f] and [g] may also be defined on some
/// domain larger than [a]. We need to be careful to ensure that merely
/// proving [f] and [g] equal on their sub-domain [a] does not lead us
/// to conclude that they are equal everywhere.
///
/// For more context on how functional extensionality works in F*, see
///   1. tests/micro-benchmarks/Test.FunctionalExtensionality.fst
///   2. ulib/FStar.Map.fst and ulib/FStar.Map.fsti
///   3. Issue #1542 on github.com/FStarLang/FStar/issues/1542

(** The type of total, dependent functions *)
unfold
let arrow (a: Type) (b: (a -> Type)) = x: a -> Tot (b x)

(** Using [arrow] instead *)
[@@ (deprecated "Use arrow instead")]
let efun (a: Type) (b: (a -> Type)) = arrow a b

(** feq #a #b f g: pointwise equality of [f] and [g] on domain [a] *)
let feq (#a: Type) (#b: (a -> Type)) (f g: arrow a b) = forall x. {:pattern (f x)\/(g x)} f x == g x

(** [on_domain a f]:

    This is a key function provided by the module. It has several
    features.

    1. Intuitively, [on_domain a f] can be seen as a function whose
       maximal domain is [a].

    2. While, [on_domain a f] is proven to be *pointwise* equal to [f],
       crucially it is not provably equal to [f], since [f] may
       actually have a domain larger than [a].

    3. [on_domain] is idempotent

    4. [on_domain a f x] has special treatment in F*'s normalizer. It
        reduces to [f x], reflecting the pointwise equality of
        [on_domain a f] and [f].

    5. [on_domain] is marked [inline_for_extraction], to eliminate the
        overhead of an indirection in extracted code. (This feature
        will be exercised as part of cross-module inlining across
        interface boundaries)
*)
inline_for_extraction
val on_domain (a: Type) (#b: (a -> Type)) ([@@@strictly_positive] f: arrow a b) : Tot (arrow a b)

(** feq_on_domain:
     [on_domain a f] is pointwise equal to [f]
 *)
val feq_on_domain (#a: Type) (#b: (a -> Type)) (f: arrow a b)
    : Lemma (feq (on_domain a f) f) [SMTPat (on_domain a f)]

(** on_domain is idempotent *)
val idempotence_on_domain (#a: Type) (#b: (a -> Type)) (f: arrow a b)
    : Lemma (on_domain a (on_domain a f) == on_domain a f) [SMTPat (on_domain a (on_domain a f))]

(** [is_restricted a f]:

     Though stated indirectly, [is_restricted a f] is valid when [f]
     is a function whose maximal domain is equal to [a].

     Equivalently, one may see its definition as
        [exists g. f == on_domain a g]
*)
let is_restricted (a: Type) (#b: (a -> Type)) (f: arrow a b) = on_domain a f == f

(** restricted_t a b:
      Lifts the [is_restricted] predicate into a refinement type

      This is the type of functions whose maximal domain is [a]
      and whose (dependent) co-domain is [b].
*)
let restricted_t (a: Type) (b: (a -> Type)) = f: arrow a b {is_restricted a f}

(** [a ^-> b]:

      Notation for non-dependent restricted functions from [a] to [b].
      The first symbol [^] makes it right associative, as expected for
      arrows.
 *)
unfold
let op_Hat_Subtraction_Greater (a b: Type) = restricted_t a (fun _ -> b)

(** [on_dom a f]:
     A convenience function to introduce a restricted, dependent function
 *)
unfold
let on_dom (a: Type) (#b: (a -> Type)) (f: arrow a b) : restricted_t a b = on_domain a f

(** [on a f]:
     A convenience function to introduce a restricted, non-dependent function
 *)
unfold
let on (a #b: Type) (f: (a -> Tot b)) : (a ^-> b) = on_dom a f

(**** MAIN AXIOM *)

(** [extensionality]:

     The main axiom of this module states that functions [f] and [g]
     that are pointwise equal on domain [a] are provably equal when
     restricted to [a] *)
val extensionality (a: Type) (b: (a -> Type)) (f g: arrow a b)
    : Lemma (ensures (feq #a #b f g <==> on_domain a f == on_domain a g)) [SMTPat (feq #a #b f g)]

(**** DUPLICATED FOR GHOST FUNCTIONS *)

(** The type of ghost, total, dependent functions *)
unfold
let arrow_g (a: Type) (b: (a -> Type)) = x: a -> GTot (b x)

(** Use [arrow_g] instead *)
[@@ (deprecated "Use arrow_g instead")]
let efun_g (a: Type) (b: (a -> Type)) = arrow_g a b

(** [feq_g #a #b f g]: pointwise equality of [f] and [g] on domain [a] **)
let feq_g (#a: Type) (#b: (a -> Type)) (f g: arrow_g a b) =
  forall x. {:pattern (f x)\/(g x)} f x == g x

(** The counterpart of [on_domain] for ghost functions *)
val on_domain_g (a: Type) (#b: (a -> Type)) (f: arrow_g a b) : Tot (arrow_g a b)

(** [on_domain_g a f] is pointwise equal to [f] *)
val feq_on_domain_g (#a: Type) (#b: (a -> Type)) (f: arrow_g a b)
    : Lemma (feq_g (on_domain_g a f) f) [SMTPat (on_domain_g a f)]

(** on_domain_g is idempotent *)
val idempotence_on_domain_g (#a: Type) (#b: (a -> Type)) (f: arrow_g a b)
    : Lemma (on_domain_g a (on_domain_g a f) == on_domain_g a f)
      [SMTPat (on_domain_g a (on_domain_g a f))]

(** Counterpart of [is_restricted] for ghost functions *)
let is_restricted_g (a: Type) (#b: (a -> Type)) (f: arrow_g a b) = on_domain_g a f == f

(** Counterpart of [restricted_t] for ghost functions *)
let restricted_g_t (a: Type) (b: (a -> Type)) = f: arrow_g a b {is_restricted_g a f}

(** [a ^->> b]:

      Notation for ghost, non-dependent restricted functions from [a]
      a to [b].
 *)
unfold
let op_Hat_Subtraction_Greater_Greater (a b: Type) = restricted_g_t a (fun _ -> b)

(** [on_dom_g a f]:
     A convenience function to introduce a restricted, ghost, dependent function
 *)
unfold
let on_dom_g (a: Type) (#b: (a -> Type)) (f: arrow_g a b) : restricted_g_t a b = on_domain_g a f

(** [on_g a f]:
     A convenience function to introduce a restricted, ghost, non-dependent function
 *)
unfold
let on_g (a #b: Type) (f: (a -> GTot b)) : (a ^->> b) = on_dom_g a f

(** Main axiom for ghost functions **)
val extensionality_g (a: Type) (b: (a -> Type)) (f g: arrow_g a b)
    : Lemma (ensures (feq_g #a #b f g <==> on_domain_g a f == on_domain_g a g))
      [SMTPat (feq_g #a #b f g)]

