(*
   Copyright 2020 Microsoft Research

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

module Steel.Effect.Common
let ( @ ) x y = FStar.List.Tot.append x y
open Steel.Memory
module Mem = Steel.Memory
module FExt = FStar.FunctionalExtensionality
open FStar.Ghost

/// This module provides various predicates and functions which are common to the
/// different Steel effects.
/// It also contains the tactic responsible for frame inference through a variant of AC-unification

#set-options "--ide_id_info_off"

(* Normalization helpers *)

irreducible let framing_implicit : unit = ()
irreducible let __steel_reduce__ : unit = ()
/// An internal attribute for finer-grained normalization in framing equalities
irreducible let __inner_steel_reduce__ : unit = ()
irreducible let __reduce__ : unit = ()
irreducible let smt_fallback : unit = ()
irreducible let ite_attr : unit = ()

// Needed to avoid some logical vs prop issues during unification with no subtyping
[@@__steel_reduce__]
unfold
let true_p : prop = True

let join_preserves_interp (hp:slprop) (m0:hmem hp) (m1:mem{disjoint m0 m1})
: Lemma
  (interp hp (join m0 m1))
  [SMTPat (interp hp (join m0 m1))]
= let open Steel.Memory in
  intro_emp m1;
  intro_star hp emp m0 m1;
  affine_star hp emp (join m0 m1)

(* Definition of a selector for a given slprop *)

/// A selector of type `a` for a separation logic predicate hp is a function
/// from a memory where the predicate hp holds, which returns a value of type `a`.
/// The effect GTot indicates that selectors are ghost functions, used for specification
/// and proof purposes only
let selector' (a:Type0) (hp:slprop) = hmem hp -> GTot a

/// Self-framing property for selectors
let sel_depends_only_on (#a:Type) (#hp:slprop) (sel:selector' a hp) =
  forall (m0:hmem hp) (m1:mem{disjoint m0 m1}).
    (interp_depends_only_on hp; (
    sel m0 == sel (join m0 m1)))

/// Additional property that selectors must satisfy, related to internals of
/// the Steel memory model encoding
let sel_depends_only_on_core (#a:Type) (#hp:slprop) (sel:selector' a hp) =
  forall (m0:hmem hp). sel m0 == sel (core_mem m0)

/// Full definition of a selector, as a function which satisfies the two predicates above
let selector (a:Type) (hp:slprop) : Type =
  sel:selector' a hp{sel_depends_only_on sel /\ sel_depends_only_on_core sel}

/// The basis of our selector framework: Separation logic assertions enhanced with selectors
/// Note that selectors are "optional", it is always possible to use a non-informative selector,
/// such as fun _ -> () and to rely on the standard separation logic reasoning
noeq
type vprop' =
  { hp: slprop u#1;
    t:Type0;
    sel: selector t hp}

(* Lifting the star operator to an inductive type makes normalization
   and implementing some later functions easier *)
[@@__steel_reduce__; erasable]
noeq
type vprop =
  | VUnit : vprop' -> vprop
  | VStar: vprop -> vprop -> vprop

(* A generic lift from slprop to vprop with a non-informative selector *)

[@@ __steel_reduce__]
let to_vprop' (p:slprop) = {hp = p; t = unit; sel = fun _ -> ()}

[@@ __steel_reduce__]
unfold
let to_vprop (p:slprop) = VUnit (to_vprop' p)

/// Normalization steps for norm below.
/// All functions marked as `unfold`, or with the `__steel_reduce__` attribute will be reduced,
/// as well as some functions internal to the selector framework
unfold
let normal_steps =
   [delta_attr [`%__steel_reduce__; `%__inner_steel_reduce__];
    delta_only [`%Mkvprop'?.t; `%Mkvprop'?.hp; `%Mkvprop'?.sel;
      `%FStar.Algebra.CommMonoid.Equiv.__proj__CM__item__mult;
      `%FStar.Algebra.CommMonoid.Equiv.__proj__CM__item__unit];
    delta_qualifier ["unfold"];
    iota;zeta;primops; simplify]

/// The core normalization primitive used to simplify Verification Conditions before encoding
/// them to an SMT solver.
unfold
let normal (#a:Type) (x:a) = norm normal_steps x

/// An abbreviation for the VStar constructor, allowing to use it with infix notation
[@@ __steel_reduce__; __reduce__]
let star = VStar

/// Extracting the underlying separation logic assertion from a vprop
[@@ __steel_reduce__]
let rec hp_of (p:vprop) = match p with
  | VUnit p -> p.hp
  | VStar p1 p2 -> hp_of p1 `Mem.star` hp_of p2

/// Extracting the selector type from a vprop
[@@ __steel_reduce__]
let rec t_of (p:vprop) = match p with
  | VUnit p -> p.t
  | VStar p1 p2 -> t_of p1 * t_of p2

/// Extracting the selector from a vprop
[@@ __steel_reduce__]
let rec sel_of (p:vprop) : GTot (selector (t_of p) (hp_of p)) = match p with
  | VUnit p -> fun h -> p.sel h
  | VStar p1 p2 ->
     let sel1 = sel_of p1 in
     let sel2 = sel_of p2 in
     fun h -> (sel1 h, sel2 h)

/// Type abbreviations for separation logic pre- and postconditions of the Steel effects
type pre_t = vprop
type post_t (a:Type) = a -> vprop

/// An annotation to indicate which separation logic predicates correspond to monadic computations
/// These computations are handled in a specific manner in the framing tactic; they correspond to places where
/// the context shrinks from all local variables in the computation to variables available at the toplevel
let return_pre (p:vprop) : vprop = p

noextract
let hmem (p:vprop) = hmem (hp_of p)

/// Abstract predicate for vprop implication. Currently implemented as an implication on the underlying slprop
val can_be_split (p q:pre_t) : Type0

/// Exposing the implementation of `can_be_split` when needed for proof purposes
val reveal_can_be_split (_:unit) : Lemma
  (forall p q. can_be_split p q == Mem.slimp (hp_of p) (hp_of q))

/// A targeted version of the above
val can_be_split_interp (r r':vprop) (h:hmem r)
  : Lemma (requires can_be_split r r')
          (ensures interp (hp_of r') h)


/// A dependent version of can_be_split, to be applied to dependent postconditions
let can_be_split_forall (#a:Type) (p q:post_t a) = forall x. can_be_split (p x) (q x)

/// A version of can_be_split which is indexed by a proposition, which can be used for equalities abduction
let can_be_split_dep (p:prop) (t1 t2:pre_t) = p ==> can_be_split t1 t2

/// A dependent version of the above predicate
let can_be_split_forall_dep (#a:Type) (p:a -> prop) (t1 t2:post_t a) =
  forall (x:a). p x ==> can_be_split (t1 x) (t2 x)

(* Some lemmas about the can_be_split* predicates,
  to be used as rewriting rules for the abstract predicates *)

val can_be_split_trans (p q r:vprop)
: Lemma
  (requires p `can_be_split` q /\ q `can_be_split` r)
  (ensures p `can_be_split` r)

let can_be_split_trans_rev (p q r:vprop)
: Lemma
  (requires q `can_be_split` r /\ p `can_be_split` q)
  (ensures p `can_be_split` r)
= can_be_split_trans p q r

val can_be_split_star_l (p q:vprop)
: Lemma
  (ensures (p `star` q) `can_be_split` p)
  [SMTPat ((p `star` q) `can_be_split` p)]

val can_be_split_star_r (p q:vprop)
: Lemma
  (ensures (p `star` q) `can_be_split` q)
  [SMTPat ((p `star` q) `can_be_split` q)]

val can_be_split_refl (p:vprop)
: Lemma (p `can_be_split` p)
[SMTPat (p `can_be_split` p)]


val can_be_split_congr_l
  (p q r: vprop)
: Lemma
  (requires (p `can_be_split` q))
  (ensures ((p `star` r) `can_be_split` (q `star` r)))

val can_be_split_congr_r
  (p q r: vprop)
: Lemma
  (requires (p `can_be_split` q))
  (ensures ((r `star` p) `can_be_split` (r `star` q)))

let prop_and (p1 p2: prop) : Tot prop = p1 /\ p2

let can_be_split_forall_dep_trans_rev
  (#a: Type)
  (cond1 cond2: a -> prop)
  (p q r: post_t a)
: Lemma
  (requires (can_be_split_forall_dep cond2 q r /\ can_be_split_forall_dep cond1 p q))
  (ensures (can_be_split_forall_dep (fun x -> cond1 x `prop_and` cond2 x) p r))
=
  Classical.forall_intro_3 (fun x y z -> Classical.move_requires (can_be_split_trans x y) z)

let can_be_split_forall_dep_congr_l
  (#a: Type)
  (cond: a -> prop)
  (p q r: post_t a)
: Lemma
  (requires (can_be_split_forall_dep cond p q))
  (ensures (can_be_split_forall_dep cond (fun x -> p x `star` r x) (fun x -> q x `star` r x)))
=
  Classical.forall_intro_3 (fun x y z -> Classical.move_requires (can_be_split_congr_l x y) z)

let can_be_split_forall_dep_congr_r
  (#a: Type)
  (cond: a -> prop)
  (p q r: post_t a)
: Lemma
  (requires (can_be_split_forall_dep cond p q))
  (ensures (can_be_split_forall_dep cond (fun x -> r x `star` p x) (fun x -> r x `star` q x)))
=
  Classical.forall_intro_3 (fun x y z -> Classical.move_requires (can_be_split_congr_r x y) z)

/// To simplify the implementation of the framing tactic, dependent equivalence
/// is defined as a double dependent implication
let equiv_forall (#a:Type) (t1 t2:post_t a) : Type0
  = t1 `can_be_split_forall` t2 /\ t2 `can_be_split_forall` t1

/// This equivalence models a context restriction at the end of a Steel computation;
/// note that t2 does not depend on the value of type `a`, but the two vprops must be
///  equivalent
let can_be_split_post (#a #b:Type) (t1:a -> post_t b) (t2:post_t b) =
  forall (x:a). equiv_forall (t1 x) t2

/// Lifting the equivalence relation to vprops. Two vprops are equivalent if the underlying slprops
/// are equivalent
val equiv (p q:vprop) : prop
/// Revealing the definition of vprop equivalence when needed for proof purposes.
/// In other cases, the predicate is abstract
val reveal_equiv (p q:vprop) : Lemma (p `equiv` q <==> hp_of p `Mem.equiv` hp_of q)

(* A restricted view of the heap,
   that only allows to access selectors of the current slprop *)

let rmem' (pre:vprop) =
  FExt.restricted_g_t
  (r0:vprop{can_be_split pre r0})
  (fun r0 -> normal (t_of r0))

/// Ensuring that rmems encapsulate the structure induced by the separation logic star
val valid_rmem (#frame:vprop) (h:rmem' frame) : prop

unfold
let rmem (pre:vprop) = h:rmem' pre{valid_rmem h}

/// Exposing the definition of mk_rmem to better normalize Steel VCs
unfold noextract
let unrestricted_mk_rmem (r:vprop) (h:hmem r) = fun (r0:vprop{r `can_be_split` r0}) ->
  can_be_split_interp r r0 h;
  sel_of r0 h

[@@ __inner_steel_reduce__]
noextract
let mk_rmem' (r:vprop) (h:hmem r) : Tot (rmem' r) =
   FExt.on_dom_g
     (r0:vprop{r `can_be_split` r0})
     (unrestricted_mk_rmem r h)

val lemma_valid_mk_rmem (r:vprop) (h:hmem r) : Lemma (valid_rmem (mk_rmem' r h))

[@@ __inner_steel_reduce__]
noextract
let mk_rmem (r:vprop) (h:hmem r) : Tot (rmem r) =
  lemma_valid_mk_rmem r h;
  mk_rmem' r h

val reveal_mk_rmem (r:vprop) (h:hmem r) (r0:vprop{r `can_be_split` r0})
  : Lemma (ensures reveal_can_be_split(); (mk_rmem r h) r0 == sel_of r0 h)

(* Logical pre and postconditions can only access the restricted view of the heap *)

type req_t (pre:pre_t) = rmem pre -> Type0
type ens_t (pre:pre_t) (a:Type) (post:post_t a) =
  rmem pre -> (x:a) -> rmem (post x) -> Type0

(* Empty assertion *)
val emp : vprop

/// When needed for proof purposes, the empty assertion is a direct lift of the
/// empty assertion from Steel.Memory
val reveal_emp (_:unit) : Lemma (hp_of emp == Mem.emp /\ t_of emp == unit)

/// Lifting pure predicates to vprop
[@@__steel_reduce__]
unfold let pure (p:prop) = to_vprop (pure p)

/// Framing predicates for the Steel effect. If the current computation has already
/// been framed, then the additional frame is the empty predicate
let maybe_emp (framed:bool) (frame:pre_t) = if framed then frame == emp else True
/// Dependent version of the above predicate, usable in dependent postconditions
let maybe_emp_dep (#a:Type) (framed:bool) (frame:post_t a) =
  if framed then (forall x. frame x == emp) else True

(* focus_rmem is an additional restriction of our view of memory.
   We expose it here to be able to reduce through normalization;
   Any valid application of focus_rmem h will be reduced to the application of h *)

[@@ __steel_reduce__]
unfold
let unrestricted_focus_rmem (#r:vprop) (h:rmem r) (r0:vprop{r `can_be_split` r0})
  = fun (r':vprop{can_be_split r0 r'}) -> can_be_split_trans r r0 r'; h r'

[@@ __inner_steel_reduce__]
let focus_rmem' (#r: vprop) (h: rmem r) (r0: vprop{r `can_be_split` r0}) : Tot (rmem' r0)
 = FExt.on_dom_g
   (r':vprop{can_be_split r0 r'})
   (unrestricted_focus_rmem h r0)

val lemma_valid_focus_rmem (#r:vprop) (h:rmem r) (r0:vprop{r `can_be_split` r0})
  : Lemma (valid_rmem (focus_rmem' h r0))

[@@ __inner_steel_reduce__]
let focus_rmem (#r:vprop) (h:rmem r) (r0:vprop{r `can_be_split` r0}) : Tot (rmem r0) =
  lemma_valid_focus_rmem h r0;
  focus_rmem' h r0

/// Exposing that calling focus_rmem on the current context corresponds to an equality
let focus_rmem_refl (r:vprop) (h:rmem r)
  : Lemma (focus_rmem #r h r == h)
  = FStar.FunctionalExtensionality.extensionality_g _ _ (focus_rmem #r h r) h

open FStar.Tactics

/// State that all "atomic" subresources have the same selectors on both views.
/// The predicate has the __steel_reduce__ attribute, ensuring that VC normalization
/// will reduce it to a conjunction of equalities on atomic subresources
/// This predicate is also marked as `strict_on_arguments` on [frame], ensuring that
/// it will not be reduced when the frame is symbolic
/// Instead, the predicate will be rewritten to an equality using `lemma_frame_equalities` below
[@@ __steel_reduce__; strict_on_arguments [0]]
let rec frame_equalities'
  (frame:vprop)
  (h0:rmem frame) (h1:rmem frame) : Type0
  = begin match frame with
    | VUnit p -> h0 frame == h1 frame
    | VStar p1 p2 ->
        can_be_split_star_l p1 p2;
        can_be_split_star_r p1 p2;

        let h01 = focus_rmem h0 p1 in
        let h11 = focus_rmem h1 p1 in

        let h02 = focus_rmem h0 p2 in
        let h12 = focus_rmem h1 p2 in


        frame_equalities' p1 h01 h11 /\
        frame_equalities' p2 h02 h12
    end

/// This lemma states that frame_equalities is the same as an equality on the top-level frame.
/// The uncommon formulation with an extra [p] is needed to use in `rewrite_with_tactic`,
/// where the goal is of the shape `frame_equalities frame h0 h1 == ?u`
/// The rewriting happens below, in `frame_vc_norm`
val lemma_frame_equalities (frame:vprop) (h0:rmem frame) (h1:rmem frame) (p:Type0)
  : Lemma
    (requires (h0 frame == h1 frame) == p)
    (ensures frame_equalities' frame h0 h1 == p)

/// A special case for frames about emp.
val lemma_frame_emp (h0:rmem emp) (h1:rmem emp) (p:Type0)
  : Lemma (requires True == p)
          (ensures frame_equalities' emp h0 h1 == p)

/// A variant of conjunction elimination, suitable to the equality goals during rewriting
val elim_conjunction (p1 p1' p2 p2':Type0)
  : Lemma (requires p1 == p1' /\ p2 == p2')
          (ensures (p1 /\ p2) == (p1' /\ p2'))

/// Normalization and rewriting step for generating frame equalities.
/// The frame_equalities function has the strict_on_arguments attribute on the [frame],
/// ensuring that it is not reduced when the frame is symbolic.
/// When that happens, we want to replace frame_equalities by an equality on the frame,
/// mimicking reduction
[@@plugin]
let frame_vc_norm () : Tac unit =
  // Do not normalize mk_rmem/focus_rmem to simplify application of
  // the reflexivity lemma on frame_equalities'
  norm [delta_attr [`%__steel_reduce__];
    delta_only [`%Mkvprop'?.t; `%Mkvprop'?.hp; `%Mkvprop'?.sel;
      `%FStar.Algebra.CommMonoid.Equiv.__proj__CM__item__mult;
      `%FStar.Algebra.CommMonoid.Equiv.__proj__CM__item__unit];
    delta_qualifier ["unfold"];
    iota;zeta;primops; simplify];

  // After reduction, the term to rewrite might be of the shape
  // (frame_equalities' ... /\ frame_equalities' .. /\ ...) == ?u,
  // with some frame_equalities' possibly already fully reduced
  // We repeatedly split the clause and extract the term on the left
  // to generate equalities on atomic subresources
  ignore (repeat (fun _ ->
    // Try to split the conjunction. If there is no conjunction, we exit the repeat
    apply_lemma (`elim_conjunction);
    // Dismiss the two uvars created for the RHS, they'll be solved by unification
    dismiss ();
    dismiss ();
    // The first goal is the left conjunction
    split ();
    // Removes the frame equality if it is about emp
    or_else (fun _ -> apply_lemma (`lemma_frame_emp); dismiss()) (fun _ -> ());
    // Rewrites the frame_equalities if it wasn't yet reduced
    or_else (fun _ -> apply_lemma (`lemma_frame_equalities); dismiss ()) (fun _ -> ());
    norm normal_steps;
    // Finally solve the uvar, finishing the rewriting for this clause
    trefl ()
  ));

  // Removes the frame equality if it is about emp
  or_else (fun _ -> apply_lemma (`lemma_frame_emp); dismiss()) (fun _ -> ());

  // We do not have conjunctions anymore, we try to apply the frame_equalities rewriting
  // If it fails, the frame was not symbolic, so there is nothing to do
  or_else (fun _ -> apply_lemma (`lemma_frame_equalities); dismiss ()) (fun _ -> ());
  norm normal_steps;
  trefl ()

[@@ __steel_reduce__]
unfold
let frame_equalities
  (frame:vprop)
  (h0:rmem frame) (h1:rmem frame) : prop
  = rewrite_with_tactic frame_vc_norm (frame_equalities' frame h0 h1)

/// More lemmas about the abstract can_be_split predicates, to be used as
/// rewriting rules in the tactic below
val can_be_split_dep_refl (p:vprop)
: Lemma (can_be_split_dep True p p)

val equiv_can_be_split (p1 p2:vprop) : Lemma
  (requires p1 `equiv` p2)
  (ensures p1 `can_be_split` p2)

val intro_can_be_split_frame (p q:vprop) (frame:vprop)
  : Lemma (requires q `equiv` (p `star` frame))
          (ensures can_be_split q p /\ True)

val can_be_split_post_elim (#a #b:Type) (t1:a -> post_t b) (t2:post_t b)
  : Lemma (requires (forall (x:a) (y:b). t1 x y `equiv` t2 y))
          (ensures t1 `can_be_split_post` t2)

val equiv_forall_refl (#a:Type) (t:post_t a)
  : Lemma (t `equiv_forall` t)

val equiv_forall_elim (#a:Type) (t1 t2:post_t a)
  : Lemma (requires (forall (x:a). t1 x `equiv` t2 x))
          (ensures t1 `equiv_forall` t2)

open FStar.Tactics.CanonCommMonoidSimple.Equiv

(* equiv is an equivalence relation on vprops *)

/// Lemmas establishing the equivalence properties on equiv
val equiv_refl (x:vprop) : Lemma (equiv x x)

val equiv_sym (x y:vprop) : Lemma
  (requires equiv x y)
  (ensures equiv y x)

val equiv_trans (x y z:vprop) : Lemma
  (requires equiv x y /\ equiv y z)
  (ensures equiv x z)

module CE = FStar.Algebra.CommMonoid.Equiv

/// Equiv is an equivalence relation for vprops elements
inline_for_extraction noextract let req : CE.equiv vprop =
  CE.EQ equiv
     equiv_refl
     equiv_sym
     equiv_trans

(* Star induces a commutative monoid for the equiv equivalence relation *)

/// Lemmas establishing the commutative monoid properties
val cm_identity (x:vprop) : Lemma ((emp `star` x) `equiv` x)

val star_commutative (p1 p2:vprop)
  : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))

val star_associative (p1 p2 p3:vprop)
  : Lemma (((p1 `star` p2) `star` p3)
           `equiv`
           (p1 `star` (p2 `star` p3)))

val star_congruence (p1 p2 p3 p4:vprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))

/// Star induces a commutative monoid on vprops
[@__steel_reduce__]
inline_for_extraction noextract let rm : CE.cm vprop req =
  CE.CM emp
     star
     cm_identity
     star_associative
     star_commutative
     star_congruence

(*** Vprop combinators ***)

(* Refining a vprop with a selector predicate *)

/// Separation logic predicate stating the validity of a vprop with an additional refinement on its selector
val vrefine_hp (v: vprop) (p: (normal (t_of v) -> Tot prop)) : Tot (slprop u#1)

/// Exposing the validity of the above predicate when needed for proof purposes
val interp_vrefine_hp (v: vprop) (p: (normal (t_of v) -> Tot prop)) (m: mem) : Lemma
  (interp (vrefine_hp v p) m <==> (interp (hp_of v) m /\ p (sel_of v m)))

/// Selector type for a refined vprop
[@__steel_reduce__]
let vrefine_t (v: vprop) (p: (normal (t_of v) -> Tot prop)) : Tot Type
= (x: t_of v {p x})

/// Selector of a refined vprop. Returns a value which satisfies the refinement predicate
val vrefine_sel (v: vprop) (p: (normal (t_of v) -> Tot prop)) : Tot (selector (vrefine_t v p) (vrefine_hp v p))

/// Exposing the definition of the refined selector
val vrefine_sel_eq (v: vprop) (p: (normal (t_of v) -> Tot prop)) (m: Mem.hmem (vrefine_hp v p)) : Lemma
  (
    interp (hp_of v) m /\
    vrefine_sel v p m == sel_of v m
  )
//  [SMTPat ((vrefine_sel v p) m)] // FIXME: this pattern causes Z3 "wrong number of argument" errors

/// Combining the above pieces to define a vprop refined by a selector prediacte
[@__steel_reduce__]
let vrefine' (v: vprop) (p: (normal (t_of v) -> Tot prop)) : Tot vprop' = {
  hp = vrefine_hp v p;
  t = vrefine_t v p;
  sel = vrefine_sel v p;
}

[@__steel_reduce__]
let vrefine (v: vprop) (p: (normal (t_of v) -> Tot prop)) = VUnit (vrefine' v p)

(* Dependent star for vprops *)

/// Separation logic predicate corresponding to a dependent star,
/// where the second predicate depends on the selector value of the first
val vdep_hp (v: vprop) (p: ( (t_of v) -> Tot vprop)) : Tot (slprop u#1)

/// Exposing the validity of the above predicate when needed for proof purposes
val interp_vdep_hp (v: vprop) (p: ( (t_of v) -> Tot vprop)) (m: mem) : Lemma
  (interp (vdep_hp v p) m <==> (interp (hp_of v) m /\ interp (hp_of v `Mem.star` hp_of (p (sel_of v m))) m))

/// Helper to define the selector type of the second component of the dependent star
let vdep_payload
  (v: vprop) (p: ( (t_of v) -> Tot vprop))
  (x: t_of v)
: Tot Type
= t_of (p x)

/// Selector type for the dependent star: A dependent tuple, where the second component's type depends on the first vprop
let vdep_t (v: vprop) (p: ( (t_of v) -> Tot vprop)) : Tot Type
= dtuple2 (t_of v) (vdep_payload v p)

/// Selector for the dependent star
val vdep_sel (v: vprop) (p: ( (t_of v) -> Tot vprop)) : Tot (selector (vdep_t v p) (vdep_hp v p))

/// Exposing the definition of the dependent star's selector when needed for proof purposes
val vdep_sel_eq (v: vprop) (p: ( (t_of v) -> Tot vprop)) (m: Mem.hmem (vdep_hp v p)) : Lemma
  (
    interp (hp_of v) m /\
    begin let x = sel_of v m in
      interp (hp_of (p x)) m /\
      vdep_sel v p m == (| x, sel_of (p x) m |)
    end
  )

/// Combining the elements above to create a dependent star vprop
[@__steel_reduce__]
let vdep' (v: vprop) (p: ( (t_of v) -> Tot vprop)) : Tot vprop' = {
  hp = vdep_hp v p;
  t = vdep_t v p;
  sel = vdep_sel v p;
}

[@__steel_reduce__]
let vdep (v: vprop) (p: ( (t_of v) -> Tot vprop)) = VUnit (vdep' v p)

(* Selector rewrite combinator *)

/// The selector of a rewrite combinator applies a function `f` to the current selector of a vprop.
val vrewrite_sel (v: vprop) (#t: Type) (f: (normal (t_of v) -> GTot t)) : Tot (selector t (normal (hp_of v)))

/// Exposing the definition of the above selector
val vrewrite_sel_eq (v: vprop) (#t: Type) (f: (normal (t_of v) -> GTot t)) (h: Mem.hmem (normal (hp_of v))) : Lemma
  ((vrewrite_sel v f <: selector' _ _) h == f ((normal (sel_of v) <: selector' _ _) h))
//  [SMTPat (vrewrite_sel v f h)] // FIXME: this pattern causes Z3 "wrong number of argument" errors


/// Combining the above elements to create a rewrite vprop
[@__steel_reduce__]
let vrewrite' (v: vprop) (#t: Type) (f: (normal (t_of v) -> GTot t)) : Tot vprop' = {
  hp = normal (hp_of v);
  t = t;
  sel = vrewrite_sel v f;
}

[@__steel_reduce__]
let vrewrite (v: vprop) (#t: Type) (f: (normal (t_of v) -> GTot t)) : Tot vprop = VUnit (vrewrite' v f)

(*** Framing tactic ***)

(* Specialize visit_tm from the standard F* tactic library to reimplement name_appears_in.
   AF: As of Jan 14, 2021, calling name_appears_in from FStar.Tactics.Derived leads to a segfault *)

exception Appears

let on_sort_bv (f : term -> Tac unit) (xbv:bv) : Tac unit =
  f (inspect_bv xbv).bv_sort

let on_sort_binder (f : term -> Tac unit) (b:binder) : Tac unit =
  let (bv, q) = inspect_binder b in
  on_sort_bv f bv

let rec visit_tm (ff : term -> Tac unit) (t : term) : Tac unit =
  let tv = inspect_ln t in
  (match tv with
  | Tv_FVar _ -> ()
  | Tv_Var bv ->
      on_sort_bv ff bv

  | Tv_BVar bv -> on_sort_bv ff bv

  | Tv_Type () -> ()
  | Tv_Const c -> ()
  | Tv_Uvar i u -> ()
  | Tv_Unknown -> ()
  | Tv_Arrow b c ->
      on_sort_binder ff b;
      visit_comp ff c
  | Tv_Abs b t ->
      let b = on_sort_binder (visit_tm ff) b in
      visit_tm ff t

  | Tv_App l (r, q) ->
       visit_tm ff l;
       visit_tm ff r

  | Tv_Refine b r ->
      visit_tm ff r

  | Tv_Let r attrs b def t ->
      visit_tm ff def;
      visit_tm ff t

  | Tv_Match sc _ brs ->
      visit_tm ff sc;
      iter (visit_br ff) brs

  | Tv_AscribedT e t topt _ ->
      visit_tm ff e;
      visit_tm ff t

  | Tv_AscribedC e c topt _ ->
      visit_tm ff e

  ); ff t

and visit_br (ff : term -> Tac unit) (b:branch) : Tac unit =
  let (p, t) = b in
  visit_tm ff t

and visit_comp (ff : term -> Tac unit) (c : comp) : Tac unit =
  let cv = inspect_comp c in
  match cv with
  | C_Total ret decr ->
      visit_tm ff ret;
      iter (visit_tm ff) decr
  | C_GTotal ret decr ->
      visit_tm ff ret;
      iter (visit_tm ff) decr

  | C_Lemma pre post pats ->
      visit_tm ff pre;
      visit_tm ff post;
      visit_tm ff pats

  | C_Eff us eff res args ->
      visit_tm ff res;
      iter (fun (a, q) -> visit_tm ff a) args

/// Decides whether a top-level name [nm] syntactically
/// appears in the term [t].
let name_appears_in (nm:name) (t:term) : Tac bool =
  let ff (t : term) : Tac unit =
    match t with
    | Tv_FVar fv -> if inspect_fv fv = nm then raise Appears
    | t -> ()
  in
  try ignore (visit_tm ff t); false with
  | Appears -> true
  | e -> raise e

/// Checks whether term [t] appears in term [i]
let term_appears_in (t:term) (i:term) : Tac bool =
  name_appears_in (explode_qn (term_to_string t)) i


/// We define a small language to handle arbitrary separation logic predicates.
/// Separation logic predicates are encoded as atoms for which equality is decidable,
/// here represented as integers
let atom : eqtype = int

let rec atoms_to_string (l:list atom) = match l with
  | [] -> ""
  | hd::tl -> string_of_int hd ^ " " ^ atoms_to_string tl

/// Reflecting the structure of our separation logic on atmos
type exp : Type =
  | Unit : exp
  | Mult : exp -> exp -> exp
  | Atom : atom -> exp

/// A map from atoms to the terms they represent.
/// The second component of the term corresponds to a default element,
/// ensuring we never raise an exception when trying to access an element in the map
let amap (a:Type) = list (atom * a) * a

/// An empty atom map: The list map is empty
let const (#a:Type) (xa:a) : amap a = ([], xa)

/// Accessing an element in the atom map
let select (#a:Type) (x:atom) (am:amap a) : Tot a =
  match List.Tot.Base.assoc #atom #a x (fst am) with
  | Some a -> a
  | _ -> snd am

/// Updating the atom map. Since select finds the first element corresponding to
/// the atom in the list and we do not have any remove function,
/// we can simply append the new element at the head without removing any possible
/// previous element
let update (#a:Type) (x:atom) (xa:a) (am:amap a) : amap a =
  (x, xa)::fst am, snd am

/// Check whether the current term is an unresolved vprop unification variable.
/// This can happen if either it is a uvar, or it is an unresolved dependent
/// vprop uvar which is applied to some argument
let is_uvar (t:term) : Tac bool = match t with
  | Tv_Uvar _ _ -> true
  | Tv_App _ _ ->
      let hd, args = collect_app t in
      Tv_Uvar? hd
  | _ -> false

/// For a given term t, collect all terms in the list l with the same head symbol
let rec get_candidates (t:term) (l:list term) : Tac (list term) =
  let name, _ = collect_app t in
  match l with
  | [] -> []
  | hd::tl ->
      let n, _ = collect_app hd in
      if term_eq n name then (
        hd::(get_candidates t tl)
      ) else get_candidates t tl

/// Try to remove a term that is exactly matching, not just that can be unified
let rec trivial_cancel (t:atom) (l:list atom) =
  match l with
  | [] -> false, l
  | hd::tl ->
      if hd = t then
        // These elements match, we remove them
        true, tl
      else (let b, res = trivial_cancel t tl in b, hd::res)

/// Call trivial_cancel on all elements of l1.
/// The first two lists returned are the remainders of l1 and l2.
/// The last two lists are the removed parts of l1 and l2, with
/// the additional invariant that they are equal
let rec trivial_cancels (l1 l2:list atom) (am:amap term)
  : Tac (list atom * list atom * list atom * list atom) =
  match l1 with
  | [] -> [], l2, [], []
  | hd::tl ->
      let b, l2'   = trivial_cancel hd l2 in
      let l1', l2', l1_del, l2_del = trivial_cancels tl l2' am in
      (if b then l1' else hd::l1'), l2',
      (if b then hd::l1_del else l1_del), (if b then hd::l2_del else l2_del)

exception Failed
exception Success

/// Helper to print the terms corresponding to the current list of atoms
let rec print_atoms (l:list atom) (am:amap term) : Tac string =
  match l with
  | [] -> ""
  | [hd] -> term_to_string (select hd am)
  | hd::tl -> term_to_string (select hd am) ^ " * " ^ print_atoms tl am

/// For a list of candidates l, count the number that can unify with t.
/// Does not try to unify with a uvar, this will be done at the very end.
/// Tries to unify with slprops with a different head symbol, it might
/// be an abbreviation
let rec try_candidates (t:atom) (l:list atom) (am:amap term) : Tac (atom * int) =
  match l with
  | [] -> t, 0
  | hd::tl ->
      if is_uvar (select hd am) then (try_candidates t tl am)
      else
        // Encapsulate unify in a try/with to ensure unification is not actually performed
        let res = try if unify (select t am) (select hd am) then raise Success else raise Failed
                  with | Success -> true | _ -> false in
        let t', n' = try_candidates t tl am in
        if res && hd <> t' then hd, 1 + n'  else t', n'

/// Remove the given term from the list. Only to be called when
/// try_candidates succeeded
let rec remove_from_list (t:atom) (l:list atom) : Tac (list atom) =
  match l with
  | [] -> fail "atom in remove_from_list not found: should not happen"; []
  | hd::tl -> if t = hd then tl else hd::remove_from_list t tl

/// Check if two lists of slprops are equivalent by recursively calling
/// try_candidates.
/// Assumes that only l2 contains terms with the head symbol unresolved.
/// It returns all elements that were not resolved during this iteration *)
let rec equivalent_lists_once (l1 l2 l1_del l2_del:list atom) (am:amap term)
  : Tac (list atom * list atom * list atom * list atom) =
  match l1 with
  | [] -> [], l2, l1_del, l2_del
  | hd::tl ->
    let t, n = try_candidates hd l2 am in
    if n = 1 then (
      let l2 = remove_from_list t l2 in
      equivalent_lists_once tl l2 (hd::l1_del) (t::l2_del) am
    ) else (
      // Either too many candidates for this scrutinee, or no candidate but the uvar
      let rem1, rem2, l1'_del, l2'_del = equivalent_lists_once tl l2 l1_del l2_del am in
      hd::rem1, rem2, l1'_del, l2'_del
    )

/// Check if two lists of slprops are equivalent by recursively calling
/// try_candidates by iterating on l2.
/// Assumes that only l2 contains terms with the head symbol unresolved.
/// It returns all elements that were not resolved during this iteration *)
/// This is very close to equivalent_lists_once above, but helps making progress
/// when l1 contains syntactically equal candidates
let rec equivalent_lists_once_l2 (l1 l2 l1_del l2_del:list atom) (am:amap term)
  : Tac (list atom * list atom * list atom * list atom) =
  match l2 with
  | [] -> l1, [], l1_del, l2_del
  | hd::tl ->
    if is_uvar (select hd am) then
      // We do not try to match the vprop uvar
      let rem1, rem2, l1'_del, l2'_del = equivalent_lists_once_l2 l1 tl l1_del l2_del am in
      rem1, hd::rem2, l1'_del, l2'_del
    else (
      let t, n = try_candidates hd l1 am in
      if n = 1 then (
        let l1 = remove_from_list t l1 in
        equivalent_lists_once_l2 l1 tl (t::l1_del) (hd::l2_del) am
      ) else (
        // Either too many candidates for this scrutinee, or no candidate but the uvar
        let rem1, rem2, l1'_del, l2'_del = equivalent_lists_once_l2 l1 tl l1_del l2_del am in
        rem1, hd::rem2, l1'_del, l2'_del
      )
    )


let get_head (l:list atom) (am:amap term) : term = match l with
  | [] -> `()
  | hd::_ -> select hd am

/// Checks whether the list of atoms [l] only contains one unresolved uvar
let is_only_uvar (l:list atom) (am:amap term) : Tac bool =
  if List.Tot.Base.length l = 1 then is_uvar (select (List.Tot.Base.hd l) am)
  else false

/// Assumes that u is a uvar, checks that all variables in l can be unified with it.
/// Later in the tactic, the uvar will be unified to a star of l *)
let rec try_unifying_remaining (l:list atom) (u:term) (am:amap term) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
      try if unify u (select hd am) then raise Success else raise Failed with
      | Success -> try_unifying_remaining tl u am
      | _ -> fail ("could not find candidate for scrutinee " ^ term_to_string (select hd am))

/// Is SMT rewriting enabled for this binder
let is_smt_binder (b:binder) : Tac bool =
  let (bv, aqual) = inspect_binder b in
  let l = snd aqual in
  not (List.Tot.isEmpty (filter (fun t -> term_eq t (`smt_fallback)) l))

/// Creates a new term, where all arguments where SMT rewriting is enabled have been replaced
/// by fresh, unconstrained unification variables
let rec new_args_for_smt_attrs (env:env) (l:list argv) (ty:typ) : Tac (list argv * list term) =
  match l, inspect ty with
  | (arg, aqualv)::tl, Tv_Arrow binder comp ->
    let needs_smt = is_smt_binder binder in
    let new_hd =
      if needs_smt then (
        let arg_ty = tc env arg in
        let uvar = fresh_uvar (Some arg_ty) in
        unshelve uvar;
        flip ();
        (uvar, aqualv)
      ) else (arg, aqualv)
    in
    begin
    match inspect_comp comp with
    | C_Total ty2 _ ->
      let tl_argv, tl_terms = new_args_for_smt_attrs env tl ty2 in
      new_hd::tl_argv, (if needs_smt then arg::tl_terms else tl_terms)
    | _ -> fail "computation type not supported in definition of slprops"
    end
  | [], Tv_FVar fv -> [], []
  | _ -> fail "should not happen. Is an slprop partially applied?"

/// Rewrites all terms in the context to enable SMT rewriting through the use of fresh, unconstrained unification variables
let rewrite_term_for_smt (env:env) (am:amap term * list term) (a:atom) : Tac (amap term * list term)
  = let am, prev_uvar_terms = am in
    let term = select a am in
    let hd, args = collect_app term in
    let t = tc env hd in
    let new_args, uvar_terms = new_args_for_smt_attrs env args t in
    let new_term = mk_app hd new_args in
    update a new_term am, uvar_terms@prev_uvar_terms

/// User-facing error message when the framing tactic fails
let fail_atoms (#a:Type) (l1 l2:list atom) (am:amap term) : Tac a
  = fail ("could not find a solution for unifying\n" ^ print_atoms l1 am ^ "\nand\n" ^ print_atoms l2 am)

/// Variant of equivalent_lists' below to be called once terms have been rewritten to allow SMT rewriting.
/// If unification succeeds and we have unicity of the solution, this tactic will succeed,
/// and ultimately create an SMT guard that the two terms are actually equal
let rec equivalent_lists_fallback (n:nat) (l1 l2 l1_del l2_del:list atom) (am:amap term)
  : Tac (list atom * list atom * bool) =
  match l1 with
  | [] -> begin match l2 with
    | [] -> (l1_del, l2_del, false)
    | [hd] ->
      // Succeed if there is only one uvar left in l2, which can be therefore
      // be unified with emp
      if is_uvar (select hd am) then (
        // xsdenote is left associative: We put hd at the top to get
        // ?u `star` p <==> emp `star` p
        (l1_del, hd :: l2_del, true))
      else fail ("could not find candidates for " ^ term_to_string (get_head l2 am))
    | _ -> fail ("could not find candidates for " ^ term_to_string (get_head l2 am))
    end
  | _ ->
    if is_only_uvar l2 am then (
      // Terms left in l1, but only a uvar left in l2.
      // Put all terms left at the end of l1_rem, so that they can be unified
      // with exactly the uvar because of the structure of xsdenote
      try_unifying_remaining l1 (get_head l2 am) am;
      l1_del @ l1, l2_del @ l2, false
    ) else
      let rem1, rem2, l1_del', l2_del' = equivalent_lists_once l1 l2 l1_del l2_del am in
      let n' = List.Tot.length rem1 in
      if n' >= n then
        // Should always be smaller or equal to n
        // If it is equal, no progress was made.
        fail_atoms rem1 rem2 am
      else equivalent_lists_fallback n' rem1 rem2 l1_del' l2_del' am

/// Iterates over all terms in [l2] to prepare them for unification with SMT rewriting
let replace_smt_uvars (l1 l2:list atom) (am:amap term) : Tac (amap term * list term)
  = let env = cur_env () in
    fold_left (rewrite_term_for_smt env) (am, []) l2

/// Recursively calls equivalent_lists_once.
/// Stops when we're done with unification, or when we didn't make any progress
/// If we didn't make any progress, we have too many candidates for some terms.
/// Accumulates rewritings of l1 and l2 in l1_del and l2_del, with the invariant
/// that the two lists are unifiable at any point
/// The boolean indicates if there is a leftover empty frame
let rec equivalent_lists' (n:nat) (use_smt:bool) (l1 l2 l1_del l2_del:list atom) (am:amap term)
  : Tac (list atom * list atom * bool * list term) =
  match l1 with
  | [] -> begin match l2 with
    | [] -> (l1_del, l2_del, false, [])
    | [hd] ->
      // Succeed if there is only one uvar left in l2, which can be therefore
      // be unified with emp
      if is_uvar (select hd am) then (
        // xsdenote is left associative: We put hd at the top to get
        // ?u `star` p <==> emp `star` p
        (l1_del, hd :: l2_del, true, []))
      else fail ("could not find candidates for " ^ term_to_string (get_head l2 am))
    | _ -> fail ("could not find candidates for " ^ term_to_string (get_head l2 am))
    end
  | _ ->
    if is_only_uvar l2 am then (
      // Terms left in l1, but only a uvar left in l2.
      // Put all terms left at the end of l1_rem, so that they can be unified
      // with exactly the uvar because of the structure of xsdenote
      try_unifying_remaining l1 (get_head l2 am) am;
      l1_del @ l1, l2_del @ l2, false, []
    ) else
      let rem1, rem2, l1_del', l2_del' = equivalent_lists_once l1 l2 l1_del l2_del am in
      let n' = List.Tot.length rem1 in
      if n' >= n then (
        // Try to make progress by matching non-uvars of l2 with candidates in l1
        let rem1, rem2, l1_del', l2_del' = equivalent_lists_once_l2 rem1 rem2 l1_del' l2_del' am in
        let n' = List.Tot.length rem1 in
        if n' >= n then (
          // Should always be smaller or equal to n
          // If it is equal, no progress was made.
          if use_smt then
            // SMT fallback is allowed
            let new_am, uvar_terms  = replace_smt_uvars rem1 rem2 am in
            let l1_f, l2_f, b = equivalent_lists_fallback n' rem1 rem2 l1_del' l2_del' new_am in
            l1_f, l2_f, b, uvar_terms
          else fail_atoms rem1 rem2 am
        ) else equivalent_lists' n' use_smt rem1 rem2 l1_del' l2_del' am
      ) else equivalent_lists' n' use_smt rem1 rem2 l1_del' l2_del' am

/// Checks if term for atom t unifies with fall uvars in l
let rec unifies_with_all_uvars (t:term) (l:list atom) (am:amap term) : Tac bool =
  match l with
  | [] -> true
  | hd::tl ->
      if unifies_with_all_uvars t tl am then (
        // Unified with tail, try this term
        let hd_t = select hd am in
        if is_uvar hd_t then (
          // The head term is a uvar, try unifying
          try if unify t hd_t then raise Success else raise Failed
          with | Success -> true | _ -> false
        ) else true // The uvar is not a head term, we do not need to try it
      ) else false

/// Puts all terms in l1 that cannot unify with the uvars in l2 at the top:
/// They need to be solved first
let rec most_restricted_at_top (l1 l2:list atom) (am:amap term) : Tac (list atom) =
  match l1 with
  | [] -> []
  | hd::tl ->
    if unifies_with_all_uvars (select hd am) l2 am then (most_restricted_at_top tl l2 am)@[hd]
    else hd::(most_restricted_at_top tl l2 am)

/// Core AC-unification tactic.
/// First remove all trivially equal terms, then try to decide equivalence.
/// Assumes that l1 does not contain any vprop uvar.
/// If it succeeds, returns permutations of l1, l2, and a boolean indicating
/// if l2 has a trailing empty frame to be unified
let equivalent_lists (use_smt:bool) (l1 l2:list atom) (am:amap term)
  : Tac (list atom * list atom * bool * list term)
= let l1, l2, l1_del, l2_del = trivial_cancels l1 l2 am in
  let l1 = most_restricted_at_top l1 l2 am in
  let n = List.Tot.length l1 in
  let l1_del, l2_del, emp_frame, uvar_terms = equivalent_lists' n use_smt l1 l2 l1_del l2_del am in
  l1_del, l2_del, emp_frame, uvar_terms

(* Helpers to relate the actual terms to their representation as a list of atoms *)

open FStar.Reflection.Derived.Lemmas

let rec list_to_string (l:list term) : Tac string =
  match l with
  | [] -> "end"
  | hd::tl -> term_to_string hd ^ " " ^ list_to_string tl

let rec mdenote_gen (#a:Type u#aa) (unit:a) (mult:a -> a -> a) (am:amap a) (e:exp) : a =
  match e with
  | Unit -> unit
  | Atom x -> select x am
  | Mult e1 e2 -> mult (mdenote_gen unit mult am e1) (mdenote_gen unit mult am e2)

let rec xsdenote_gen (#a:Type) (unit:a) (mult:a -> a -> a) (am:amap a) (xs:list atom) : a =
  match xs with
  | [] -> unit
  | [x] -> select x am
  | x::xs' -> mult (select x am) (xsdenote_gen unit mult am xs')

unfold
let mdenote (#a:Type u#aa) (eq:CE.equiv a) (m:CE.cm a eq) (am:amap a) (e:exp) : a =
  let open FStar.Algebra.CommMonoid.Equiv in
  mdenote_gen (CM?.unit m) (CM?.mult m) am e

unfold
let xsdenote (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (am:amap a) (xs:list atom) : a =
  let open FStar.Algebra.CommMonoid.Equiv in
  xsdenote_gen (CM?.unit m) (CM?.mult m) am xs

let rec flatten (e:exp) : list atom =
  match e with
  | Unit -> []
  | Atom x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2

let rec flatten_correct_aux (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (am:amap a) (xs1 xs2:list atom)
  : Lemma (xsdenote eq m am (xs1 @ xs2) `CE.EQ?.eq eq` CE.CM?.mult m (xsdenote eq m am xs1)
                                                                     (xsdenote eq m am xs2)) =
  let open FStar.Algebra.CommMonoid.Equiv in
  match xs1 with
  | [] ->
      CM?.identity m (xsdenote eq m am xs2);
      EQ?.symmetry eq (CM?.mult m (CM?.unit m) (xsdenote eq m am xs2)) (xsdenote eq m am xs2)
  | [x] -> (
      if (Nil? xs2)
      then (right_identity eq m (select x am);
            EQ?.symmetry eq (CM?.mult m (select x am) (CM?.unit m)) (select x am))
      else EQ?.reflexivity eq (CM?.mult m (xsdenote eq m am [x]) (xsdenote eq m am xs2)))
  | x::xs1' ->
      flatten_correct_aux eq m am xs1' xs2;
      EQ?.reflexivity eq (select x am);
      CM?.congruence m (select x am) (xsdenote eq m am (xs1' @ xs2))
                       (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2));
      CM?.associativity m (select x am) (xsdenote eq m am xs1') (xsdenote eq m am xs2);
      EQ?.symmetry eq (CM?.mult m (CM?.mult m (select x am) (xsdenote eq m am xs1')) (xsdenote eq m am xs2))
                      (CM?.mult m (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2)));
      EQ?.transitivity eq (CM?.mult m (select x am) (xsdenote eq m am (xs1' @ xs2)))
                          (CM?.mult m (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2)))
                          (CM?.mult m (CM?.mult m (select x am) (xsdenote eq m am xs1')) (xsdenote eq m am xs2))

let rec flatten_correct (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (am:amap a) (e:exp)
  : Lemma (mdenote eq m am e `CE.EQ?.eq eq` xsdenote eq m am (flatten e)) =
  let open FStar.Algebra.CommMonoid.Equiv in
  match e with
  | Unit -> EQ?.reflexivity eq (CM?.unit m)
  | Atom x -> EQ?.reflexivity eq (select x am)
  | Mult e1 e2 ->
      flatten_correct_aux eq m am (flatten e1) (flatten e2);
      EQ?.symmetry eq (xsdenote eq m am (flatten e1 @ flatten e2))
                      (CM?.mult m (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2)));
      flatten_correct eq m am e1;
      flatten_correct eq m am e2;
      CM?.congruence m (mdenote eq m am e1) (mdenote eq m am e2)
                       (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2));
      EQ?.transitivity eq (CM?.mult m (mdenote eq m am e1) (mdenote eq m am e2))
                          (CM?.mult m (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2)))
                          (xsdenote eq m am (flatten e1 @ flatten e2))

let monoid_reflect (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (am:amap a) (e1 e2:exp)
    (_ : squash (xsdenote eq m am (flatten e1) `CE.EQ?.eq eq` xsdenote eq m am (flatten e2)))
       : squash (mdenote eq m am e1 `CE.EQ?.eq eq` mdenote eq m am e2) =
    flatten_correct eq m am e1;
    flatten_correct eq m am e2;
    CE.EQ?.symmetry eq (mdenote eq m am e2) (xsdenote eq m am (flatten e2));
    CE.EQ?.transitivity eq
      (xsdenote eq m am (flatten e1))
      (xsdenote eq m am (flatten e2))
      (mdenote eq m am e2);
    CE.EQ?.transitivity eq
      (mdenote eq m am e1)
      (xsdenote eq m am (flatten e1))
      (mdenote eq m am e2)

// Here we sort the variable numbers

let permute = list atom -> list atom
let sort : permute = List.Tot.Base.sortWith #int (List.Tot.Base.compare_of_bool (<))

#push-options "--fuel 1 --ifuel 1"

let lemma_xsdenote_aux (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (am:amap a) (hd:atom) (tl:list atom)
  : Lemma (xsdenote eq m am (hd::tl) `CE.EQ?.eq eq`
         (CE.CM?.mult m (select hd am) (xsdenote eq m am tl)))
  = let open FStar.Algebra.CommMonoid.Equiv in
    match tl with
    | [] ->
      assert (xsdenote eq m am (hd::tl) == select hd am);
      CM?.identity m (select hd am);
      EQ?.symmetry eq (CM?.unit m `CM?.mult m` select hd am) (select hd am);
      CM?.commutativity m (CM?.unit m) (select hd am);
      EQ?.transitivity eq
        (xsdenote eq m am (hd::tl))
        (CM?.unit m `CM?.mult m` select hd am)
        (CM?.mult m (select hd am) (xsdenote eq m am tl))
    | _ -> EQ?.reflexivity eq (xsdenote eq m am (hd::tl))

let rec partition_equiv (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (am:amap a) (pivot:atom) (q:list atom)
  : Lemma
    (let open FStar.List.Tot.Base in
     let hi, lo = partition (bool_of_compare (compare_of_bool (<)) pivot) q in
     CE.EQ?.eq eq
      (xsdenote eq m am hi `CE.CM?.mult m` xsdenote eq m am lo)
      (xsdenote eq m am q))
   = let open FStar.Algebra.CommMonoid.Equiv in
     let open FStar.List.Tot.Base in
     let f = bool_of_compare (compare_of_bool (<)) pivot in
     let hi, lo = partition f q in
     match q with
     | [] -> CM?.identity m (xsdenote eq m am hi)
     | hd::tl ->
         let l1, l2 = partition f tl in
         partition_equiv eq m am pivot tl;
         assert (EQ?.eq eq
           (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2)
           (xsdenote eq m am tl));

         EQ?.reflexivity eq (xsdenote eq m am l1);
         EQ?.reflexivity eq (xsdenote eq m am l2);
         EQ?.reflexivity eq (xsdenote eq m am hi);
         EQ?.reflexivity eq (xsdenote eq m am lo);


         if f hd then begin
           assert (hi == hd::l1 /\ lo == l2);
           lemma_xsdenote_aux eq m am hd l1;
           CM?.congruence m
             (xsdenote eq m am hi)
             (xsdenote eq m am lo)
             (select hd am `CM?.mult m` xsdenote eq m am l1)
             (xsdenote eq m am l2);
           CM?.associativity m
             (select hd am)
             (xsdenote eq m am l1)
             (xsdenote eq m am l2);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             ((select hd am `CM?.mult m` xsdenote eq m am l1) `CM?.mult m` xsdenote eq m am l2)
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2));

           EQ?.reflexivity eq (select hd am);
           CM?.congruence m
             (select hd am)
             (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2)
             (select hd am)
             (xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2))
             (select hd am `CM?.mult m` xsdenote eq m am tl);

           lemma_xsdenote_aux eq m am hd tl;
           EQ?.symmetry eq
             (xsdenote eq m am (hd::tl))
             (select hd am `CM?.mult m` xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` xsdenote eq m am tl)
             (xsdenote eq m am (hd::tl))

         end else begin
           assert (hi == l1 /\ lo == hd::l2);
           lemma_xsdenote_aux eq m am hd l2;
           CM?.congruence m
             (xsdenote eq m am hi)
             (xsdenote eq m am lo)
             (xsdenote eq m am l1)
             (select hd am `CM?.mult m` xsdenote eq m am l2);
           CM?.commutativity m
             (xsdenote eq m am l1)
             (select hd am `CM?.mult m` xsdenote eq m am l2);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (xsdenote eq m am l1 `CM?.mult m` (select hd am `CM?.mult m` xsdenote eq m am l2))
             ((select hd am `CM?.mult m` xsdenote eq m am l2) `CM?.mult m` xsdenote eq m am l1);

           CM?.associativity m
             (select hd am)
             (xsdenote eq m am l2)
             (xsdenote eq m am l1);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             ((select hd am `CM?.mult m` xsdenote eq m am l2) `CM?.mult m` xsdenote eq m am l1)
             (select hd am `CM?.mult m` (xsdenote eq m am l2 `CM?.mult m` xsdenote eq m am l1));

           CM?.commutativity m (xsdenote eq m am l2) (xsdenote eq m am l1);
           EQ?.reflexivity eq (select hd am);
           CM?.congruence m
             (select hd am)
             (xsdenote eq m am l2 `CM?.mult m` xsdenote eq m am l1)
             (select hd am)
             (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` (xsdenote eq m am l2 `CM?.mult m` xsdenote eq m am l1))
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2));

           CM?.congruence m
             (select hd am)
             (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2)
             (select hd am)
             (xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2))
             (select hd am `CM?.mult m` xsdenote eq m am tl);

           lemma_xsdenote_aux eq m am hd tl;
           EQ?.symmetry eq
             (xsdenote eq m am (hd::tl))
             (select hd am `CM?.mult m` xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` xsdenote eq m am tl)
             (xsdenote eq m am (hd::tl))
         end

let rec sort_correct_aux (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (am:amap a) (xs:list atom)
  : Lemma (requires True)
          (ensures xsdenote eq m am xs `CE.EQ?.eq eq` xsdenote eq m am (sort xs))
          (decreases (FStar.List.Tot.Base.length xs))
  = let open FStar.Algebra.CommMonoid.Equiv in
  match xs with
  | [] -> EQ?.reflexivity eq (xsdenote eq m am [])
  | pivot::q ->
      let open FStar.List.Tot.Base in
      let f:int -> int -> int = compare_of_bool (<) in
      let hi, lo = partition (bool_of_compare f pivot) q in
      flatten_correct_aux eq m am (sort lo) (pivot::sort hi);
      assert (xsdenote eq m am (sort xs) `EQ?.eq eq`
        CM?.mult m (xsdenote eq m am (sort lo))
                   (xsdenote eq m am (pivot::sort hi)));

      lemma_xsdenote_aux eq m am pivot (sort hi);

      EQ?.reflexivity eq (xsdenote eq m am (sort lo));
      CM?.congruence m
        (xsdenote eq m am (sort lo))
        (xsdenote eq m am (pivot::sort hi))
        (xsdenote eq m am (sort lo))
        (select pivot am `CM?.mult m` xsdenote eq m am (sort hi));
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (xsdenote eq m am (sort lo) `CM?.mult m` xsdenote eq m am (pivot::sort hi))
        (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi)));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi))));

      CM?.commutativity m
        (xsdenote eq m am (sort lo))
        (select pivot am `CM?.mult m` xsdenote eq m am (sort hi));
      CM?.associativity m
        (select pivot am)
        (xsdenote eq m am (sort hi))
        (xsdenote eq m am (sort lo));
      EQ?.transitivity eq
         (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi)))
        ((select pivot am `CM?.mult m` xsdenote eq m am (sort hi)) `CM?.mult m` xsdenote eq m am (sort lo))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo)));
      EQ?.transitivity eq
         (xsdenote eq m am (sort xs))
         (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi)))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo)));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo))));


      partition_length (bool_of_compare f pivot) q;
      sort_correct_aux eq m am hi;
      sort_correct_aux eq m am lo;
      EQ?.symmetry eq (xsdenote eq m am lo) (xsdenote eq m am (sort lo));
      EQ?.symmetry eq (xsdenote eq m am hi) (xsdenote eq m am (sort hi));
      CM?.congruence m
        (xsdenote eq m am (sort hi))
        (xsdenote eq m am (sort lo))
        (xsdenote eq m am hi)
        (xsdenote eq m am lo);
      assert (EQ?.eq eq
        (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo))
        (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo));

      EQ?.reflexivity eq (select pivot am);
      CM?.congruence m
        (select pivot am)
        (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo))
        (select pivot am)
        (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo);
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo)))
        (select pivot am `CM?.mult m` (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)));

      partition_equiv eq m am pivot q;
      CM?.congruence m
        (select pivot am)
        (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
        (select pivot am)
        (xsdenote eq m am q);
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo))
        (select pivot am `CM?.mult m` (xsdenote eq m am q));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am q)));

      lemma_xsdenote_aux eq m am pivot q;
      EQ?.symmetry eq
        (xsdenote eq m am (pivot::q))
        (select pivot am `CM?.mult m` (xsdenote eq m am q));
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am q))
        (xsdenote eq m am xs);
      EQ?.symmetry eq (xsdenote eq m am (sort xs)) (xsdenote eq m am xs)

#pop-options

#push-options "--fuel 0 --ifuel 0"

(* Lemmas to be called after a permutation compatible with AC-unification was found *)

let smt_reflexivity (#a:Type) (eq:CE.equiv a) (x y:a)
  : Lemma (requires x == y)
          (ensures CE.EQ?.eq eq x y)
  = CE.EQ?.reflexivity eq x

let identity_left_smt (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (x y:a)
  : Lemma
    (requires x == y)
    (ensures CE.EQ?.eq eq x (CE.CM?.mult m (CE.CM?.unit m) y))
  = CE.CM?.identity m x;
    CE.EQ?.symmetry eq (CE.CM?.mult m (CE.CM?.unit m) x) x

let identity_left (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (x:a)
  : Lemma (CE.EQ?.eq eq x (CE.CM?.mult m (CE.CM?.unit m) x))
  = CE.CM?.identity m x;
    CE.EQ?.symmetry eq (CE.CM?.mult m (CE.CM?.unit m) x) x

let identity_right_diff (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (x y:a) : Lemma
  (requires CE.EQ?.eq eq x y)
  (ensures CE.EQ?.eq eq (CE.CM?.mult m x (CE.CM?.unit m)) y)
  = CE.right_identity eq m x;
    CE.EQ?.transitivity eq (CE.CM?.mult m x (CE.CM?.unit m)) x y

/// Dismiss possible vprops goals that might have been created by lemma application.
/// These vprops will be instantiated at a later stage; else, Meta-F* will raise an error
let rec dismiss_slprops () : Tac unit =
  match term_as_formula' (cur_goal ()) with
    | App t _ -> if term_eq t (`squash) then () else (dismiss(); dismiss_slprops ())
    | _ -> dismiss(); dismiss_slprops ()

/// Recursively removing trailing empty assertions
let rec n_identity_left (n:int) (eq m:term) : Tac unit
  = if n = 0 then (
      apply_lemma (`(CE.EQ?.reflexivity (`#eq)));
      // Cleaning up, in case a uvar has been generated here. It'll be solved later
      set_goals [])
    else (
      apply_lemma (`identity_right_diff (`#eq) (`#m));
      // Drop the slprops generated, they will be solved later
      dismiss_slprops ();
      n_identity_left (n-1) eq m
    )

/// Helper lemma: If two vprops (as represented by lists of atoms) are equivalent, then their canonical forms
/// (corresponding to applying the sort function on atoms) are equivalent
let equivalent_sorted (#a:Type) (eq:CE.equiv a) (m:CE.cm a eq) (am:amap a) (l1 l2 l1' l2':list atom)
    : Lemma (requires
              sort l1 == sort l1' /\
              sort l2 == sort l2' /\
              xsdenote eq m am l1 `CE.EQ?.eq eq` xsdenote eq m am l2)
           (ensures xsdenote eq m am l1' `CE.EQ?.eq eq` xsdenote eq m am l2')
  = let open FStar.Algebra.CommMonoid.Equiv in
    sort_correct_aux eq m am l1';
    sort_correct_aux eq m am l1;
    EQ?.symmetry eq (xsdenote eq m am l1) (xsdenote eq m am (sort l1));
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am (sort l1'))
      (xsdenote eq m am l1);
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am l1)
      (xsdenote eq m am l2);
    sort_correct_aux eq m am l2;
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am l2)
      (xsdenote eq m am (sort l2));
    sort_correct_aux eq m am l2';
    EQ?.symmetry eq (xsdenote eq m am l2') (xsdenote eq m am (sort l2'));
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am (sort l2))
      (xsdenote eq m am l2')

#pop-options

/// Finds the position of first occurrence of x in xs.
/// This is now specialized to terms and their funny term_eq.
let rec where_aux (n:nat) (x:term) (xs:list term) :
    Tot (option nat) (decreases xs) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

let fatom (t:term) (ts:list term) (am:amap term) : Tac (exp * list term * amap term) =
  match where t ts with
  | Some v -> (Atom v, ts, am)
  | None ->
    let vfresh = List.Tot.Base.length ts in
    let t = norm_term [iota; zeta] t in
    (Atom vfresh, ts @ [t], update vfresh t am)

/// Transforming a term into the corresponding list of atoms
/// If the atomic terms were already present in the map [am], then
/// they correspond to the same atoms
/// This expects that mult, unit, and t have already been normalized
let rec reification_aux (ts:list term) (am:amap term)
                        (mult unit t : term) : Tac (exp * list term * amap term) =
  let hd, tl = collect_app_ref t in
  match inspect hd, List.Tot.Base.list_unref tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then (let (e1, ts, am) = reification_aux ts am mult unit t1 in
          let (e2, ts, am) = reification_aux ts am mult unit t2 in
          (Mult e1 e2, ts, am))
    else fatom t ts am
  | _, _ ->
    if term_eq t unit
    then (Unit, ts, am)
    else fatom t ts am

/// Performs the required normalization before calling the function above
let reification (eq: term) (m: term) (ts:list term) (am:amap term) (t:term) :
    Tac (exp * list term * amap term) =
  let mult = norm_term [iota; zeta; delta] (`CE.CM?.mult (`#m)) in
  let unit = norm_term [iota; zeta; delta] (`CE.CM?.unit (`#m)) in
  let t    = norm_term [iota; zeta] t in
  reification_aux ts am mult unit t

/// Meta-F* internal: Transforms the atom map into a term
let rec convert_map (m : list (atom * term)) : term =
  match m with
  | [] -> `[]
  | (a, t)::ps ->
      let a = pack_ln (Tv_Const (C_Int a)) in
      (* let t = norm_term [delta] t in *)
      `((`#a, (`#t)) :: (`#(convert_map ps)))


/// `am` is an amap (basically a list) of terms, each representing a value
/// of type `a` (whichever we are canonicalizing). This functions converts
/// `am` into a single `term` of type `amap a`, suitable to call `mdenote` with *)
let convert_am (am : amap term) : term =
  let (map, def) = am in
  (* let def = norm_term [delta] def in *)
  `( (`#(convert_map map), `#def) )

/// Transforms a term representatoin into a term through quotation
let rec quote_exp (e:exp) : term =
    match e with
    | Unit -> (`Unit)
    | Mult e1 e2 -> (`Mult (`#(quote_exp e1)) (`#(quote_exp e2)))
    | Atom n -> let nt = pack_ln (Tv_Const (C_Int n)) in
                (`Atom (`#nt))

let rec quote_atoms (l:list atom) = match l with
  | [] -> `[]
  | hd::tl -> let nt = pack_ln (Tv_Const (C_Int hd)) in
              (`Cons (`#nt) (`#(quote_atoms tl)))

/// Some internal normalization steps to make reflection of vprops into atoms and atom permutation go smoothly.
/// In particular, all the sorting/list functions are entirely reduced
let normal_tac_steps = [primops; iota; zeta; delta_only [
          `%mdenote; `%select;
          `%List.Tot.Base.assoc; `%List.Tot.Base.append; `%( @ );
          `%flatten; `%sort;
          `%List.Tot.Base.sortWith; `%List.Tot.Base.partition;
          `%List.Tot.Base.bool_of_compare; `%List.Tot.Base.compare_of_bool;
          `%fst; `%__proj__Mktuple2__item___1;
          `%snd; `%__proj__Mktuple2__item___2;
          `%CE.__proj__CM__item__unit;
          `%CE.__proj__CM__item__mult;
          `%rm]]

/// The normalization function, using the above normalization steps
let normal_tac (#a:Type) (x:a) : a = FStar.Pervasives.norm normal_tac_steps x

/// Helper lemma to establish relation between normalized and initial values
let normal_elim (x:Type0) : Lemma
  (requires x)
  (ensures normal_tac x)
  = ()

exception Result of list atom * list atom * bool * list term

/// F* equalities are typed, but the generated type sometimes is a unification variable.
/// This helper ensures that such unification variables are not left unresolved, which would lead to an error
let close_equality_typ' (t:term) : Tac unit =
  let f = term_as_formula' t in
  match f with
  | Comp (Eq (Some u)) l _ -> if is_uvar u then (unshelve u; exact_with_ref (tc (cur_env()) l))
  | _ -> ()

/// Recursively closing equality types in a given term (usually a unification constraint)
let close_equality_typ (t:term) : Tac unit =
  visit_tm close_equality_typ' t

/// Core unification tactic.
/// Transforms terms into their atom representations,
/// Tries to find a solution to AC-unification, and if so,
/// soundly permutes the atom representations before calling the unifier
/// to check the validity of the provided solution.
/// In the case where SMT rewriting was needed, equalities abduction is performed by instantiating the
/// abduction prop unification variable with the corresponding guard


/// 09/24:
///
/// The tactic internally builds a map from atoms to terms
///   and uses the map for reflecting the goal to atoms representation
/// During reflection, the tactics engine typechecks the amap, and hence all
///   the terms again
/// This typechecking of terms is unnecessary, since the terms are coming
///   from the goal, and hence are already well-typed
/// Worse, re-typechecking them may generate a lot of SMT queries
/// And even worse, the SMT queries are discharged in the static context,
///   requiring various workarounds (e.g. squash variables for if conditions etc.)
///
/// To fix this, we now "name" the terms and use the amap with names
///
/// Read through the canon_l_r function for how we do this


/// The following three lemmas are helpers to manipulate the goal in canon_l_r

let inst_bv (#a:Type) (#p:a -> Type0) (#q:Type0) (x:a) (_:squash (p x ==> q))
  : Lemma ((forall (x:a). p x) ==> q) = ()

let modus_ponens (#p #q:Type0) (_:squash p)
  : Lemma ((p ==> q) ==> q)
  = ()

let cut (p q:Type0) : Lemma (requires p /\ (p ==> q)) (ensures q) = ()

let and_true (p: Type0) : Lemma (requires (p /\ True)) (ensures p) = ()

let rec unify_pr_with_true (pr: term) : Tac unit =
  let hd, tl = collect_app pr in
  if hd `term_eq` (`(/\)) || hd `term_eq` (`prop_and)
  then
    match tl with
    | [pr_l, _; pr_r, _] ->
      unify_pr_with_true pr_l;
      unify_pr_with_true pr_r
    | _ -> fail "unify_pr_with_true: ill-formed /\\"
  else
    match inspect hd with
    | Tv_Uvar _ _ -> 
      if unify pr (`true_p)
      then ()
      else begin
        fail "unify_pr_with_true: could not unify SMT prop with True"
      end
    | _ ->
      if List.Tot.length (free_uvars pr) = 0
      then ()
      else fail "unify_pr_with_true: some uvars are still there"

let elim_and_l_squash (#a #b: Type0) (#goal: Type0) (f: (a -> Tot (squash goal))) (h: (a /\ b)) : Tot (squash goal) =
  let f' (x: squash a) : Tot (squash goal) =
    FStar.Squash.bind_squash x f
  in
  let elim_impl (x: squash (a /\ b)) : Tot (squash a) = () in
  f' (elim_impl (FStar.Squash.return_squash h))

let elim_and_r_squash (#a #b: Type0) (#goal: Type0) (f: (b -> Tot (squash goal))) (h: (a /\ b)) : Tot (squash goal) =
  let f' (x: squash b) : Tot (squash goal) =
    FStar.Squash.bind_squash x f
  in
  let elim_impl (x: squash (a /\ b)) : Tot (squash b) = () in
  f' (elim_impl (FStar.Squash.return_squash h))

let _return_squash (#a: Type) () (x: a) : Tot (squash a) =
  FStar.Squash.return_squash x

let rec set_abduction_variable_term (pr: term) : Tac term =
  let hd, tl = collect_app pr in
  if hd `term_eq` (`(/\)) || hd `term_eq` (`prop_and)
  then
    match tl with
    | (pr_l, Q_Explicit) :: (pr_r, Q_Explicit) :: [] ->
      if List.Tot.length (free_uvars pr_r) = 0
      then
        let arg = set_abduction_variable_term pr_l in
        mk_app (`elim_and_l_squash) [arg, Q_Explicit]
      else if List.Tot.length (free_uvars pr_l) = 0
      then
        let arg = set_abduction_variable_term pr_r in
        mk_app (`elim_and_r_squash) [arg, Q_Explicit]
      else
        fail "set_abduction_variable_term: there are still uvars on both sides of l_and"
    | _ -> fail "set_abduction_variable: ill-formed /\\"
  else
    match hd with
    | Tv_Uvar _ _ ->
      mk_app (`_return_squash) [`(), Q_Explicit]
    | _ -> fail "set_abduction_variable: cannot unify"

let set_abduction_variable () : Tac unit =
  let g = cur_goal () in
  match inspect g with
  | Tv_Arrow b _ ->
    let (bv, _) = inspect_binder b in
    let bv = inspect_bv bv in
    let pr = bv.bv_sort in
    exact (set_abduction_variable_term pr)
  | _ -> fail "Not an arrow goal"

let canon_l_r (use_smt:bool)
  (carrier_t:term)  //e.g. vprop
  (eq:term) (m:term)
  (pr pr_bind:term)
  (lhs rel rhs:term) : Tac unit =

  let m_unit = norm_term [iota; zeta; delta] (`(CE.CM?.unit (`#m))) in
  let m_mult = norm_term [iota; zeta; delta] (`(CE.CM?.mult (`#m))) in

  let am = const m_unit in (* empty map *)
  let (r1_raw, ts, am) = reification eq m [] am lhs in
  let (r2_raw,  _, am) = reification eq m ts am rhs in

  // Encapsulating this in a try/with to avoid spawning uvars for smt_fallback
  let l1_raw, l2_raw, emp_frame, uvar_terms =
    try
      let res = equivalent_lists use_smt (flatten r1_raw) (flatten r2_raw) am in
      raise (Result res) with
    | TacticFailure m -> fail m
    | Result res -> res
    | _ -> fail "uncaught exception in equivalent_lists"
  in

   //So now we have:
   //  am     : amap mapping atoms to terms in lhs and rhs
   //  r1_raw : an expression in the atoms language for lhs
   //  r2_raw : an expression in the atoms language for rhs
   //  l1_raw : sorted list of atoms in lhs
   //  l2_raw : sorted list of atoms in rhs
   //
   //In particular, r1_raw and r2_raw capture lhs and rhs structurally
   //  (i.e. same associativity, emp, etc.)
   //
   //Whereas l1_raw and l2_raw are "canonical" representations of lhs and rhs
   //  (vis xsdenote)


  //Build an amap where atoms are mapped to names
  //The type of these names is carrier_t passed by the caller

  let am_bv : list (atom & bv) = mapi (fun i (a, _) ->
    let x = fresh_bv_named ("x" ^ (string_of_int i)) carrier_t in
    (a, x)) (fst am) in

  let am_bv_term : amap term = map (fun (a, bv) -> a, pack (Tv_Var bv)) am_bv, snd am in

  let mdenote_tm (e:exp) : term = mdenote_gen
    m_unit
    (fun t1 t2 -> mk_app m_mult [(t1, Q_Explicit); (t2, Q_Explicit)])
    am_bv_term
    e in

  let xsdenote_tm (l:list atom) : term = xsdenote_gen
    m_unit
    (fun t1 t2 -> mk_app m_mult [(t1, Q_Explicit); (t2, Q_Explicit)])
    am_bv_term
    l in

  //Get the named representations of lhs, rhs, and their respective sorted versions

  let lhs_named = mdenote_tm r1_raw in
  let rhs_named = mdenote_tm r2_raw in

  let sorted_lhs_named = xsdenote_tm l1_raw in
  let sorted_rhs_named = xsdenote_tm l2_raw in

  //We now build an auxiliary goal of the form:
  //
  //  forall xs. (sorted_lhs_named `rel` sorted_rhs_names) ==> (lhs_names `rel` rhs_named)
  //
  //  where xs are the fresh names that we introduced earlier

  let mk_rel (l r:term) : term =
    mk_app rel [(l, Q_Explicit); (r, Q_Explicit)] in

  let imp_rhs = mk_rel lhs_named rhs_named in
  let imp_lhs = mk_rel sorted_lhs_named sorted_rhs_named in

  let imp =
    mk_app (pack (Tv_FVar (pack_fv imp_qn))) [(imp_lhs, Q_Explicit); (imp_rhs, Q_Explicit)] in

  //fold over names and quantify over them

  let aux_goal = fold_right (fun (_, bv) t ->
    let b = pack_binder bv Q_Explicit [] in
    let t = close_term b t in
    let t = pack_ln (Tv_Abs b t) in
    mk_app (pack (Tv_FVar (pack_fv forall_qn))) [t, Q_Explicit]) am_bv imp in


  //Introduce a cut with the auxiliary goal

  apply_lemma (`cut (`#aux_goal));


  //After the cut, the goal looks like: A /\ (A ==> G)
  //  where A is the auxiliary goal and G is the original goal (lhs `rel` rhs)

  split ();

  //Solving A:

  focus (fun _ ->
    //The proof follows a similar structure as before naming was introduced
    //
    //Except that this time, the amap is in terms of names,
    //  and hence its typechecking is faster and (hopefully) no SMT involved

    //Open the forall binders in A, and use the fresh names to build an amap

    let am = fold_left (fun am (a, _) ->
      let b = forall_intro () in
      let bv, _ = inspect_binder b in
      (a, pack (Tv_Var bv))::am) [] am_bv, snd am in

    //Introduce the lhs of implication

    let b = implies_intro () in

    //Now the proof is the plain old canon proof

    let am = convert_am am in
    let r1 = quote_exp r1_raw in
    let r2 = quote_exp r2_raw in

    change_sq (`(normal_tac (mdenote (`#eq) (`#m) (`#am) (`#r1)
                   `CE.EQ?.eq (`#eq)`
                 mdenote (`#eq) (`#m) (`#am) (`#r2))));

    apply_lemma (`normal_elim);
    apply (`monoid_reflect );

    let l1 = quote_atoms l1_raw in
    let l2 = quote_atoms l2_raw in

    apply_lemma (`equivalent_sorted (`#eq) (`#m) (`#am) (`#l1) (`#l2));

    if List.Tot.length (goals ()) = 0 then ()
    else begin
      norm [primops; iota; zeta; delta_only
        [`%xsdenote; `%select;
         `%List.Tot.Base.assoc; `%List.Tot.Base.append; `%( @ );
         `%flatten; `%sort;
         `%List.Tot.Base.sortWith; `%List.Tot.Base.partition;
         `%List.Tot.Base.bool_of_compare; `%List.Tot.Base.compare_of_bool;
         `%fst; `%__proj__Mktuple2__item___1;
         `%snd; `%__proj__Mktuple2__item___2;
         `%CE.__proj__CM__item__unit;
         `%CE.__proj__CM__item__mult;
         `%rm;
         `%CE.__proj__EQ__item__eq;
         `%req;
         `%star;]
      ];

      //The goal is of the form G1 /\ G2 /\ G3, as in the requires of equivalent_sorted

      split ();
      split ();

      //Solve G1 and G2 by trefl

      trefl ();
      trefl ();

      //G3 is the lhs of the implication in the auxiliary goal
      //  that we have in our assumptions via b

      apply (`FStar.Squash.return_squash);
      exact (binder_to_term b)
    end);

  dismiss_slprops();

  //Our goal now is A ==> G (where G is the original goal (lhs `rel` rhs))

  //Open the forall binders

  ignore (repeatn (List.Tot.length am_bv) (fun _ -> apply_lemma (`inst_bv)));

  //And apply modus ponens

  apply_lemma (`modus_ponens);


  //Now our goal is sorted_lhs_named `rel` sorted_rhs_named
  //  where the names are replaced with fresh uvars (from the repeatn call above)

  //So we just trefl

  match uvar_terms with
  | [] -> // Closing unneeded prop uvar
    focus (fun _ ->
      try
        apply_lemma (`and_true);
        split ();
        if emp_frame then apply_lemma (`identity_left (`#eq) (`#m))
        else apply_lemma (`(CE.EQ?.reflexivity (`#eq)));
        unify_pr_with_true pr; // MUST be done AFTER identity_left/reflexivity, which can unify other uvars
        trivial ()
      with _ -> fail "Cannot unify pr with true"
    )
  | l ->
    if emp_frame then (
      apply_lemma (`identity_left_smt (`#eq) (`#m))
    ) else (
      apply_lemma (`smt_reflexivity (`#eq))
    );
    t_trefl true;
    close_equality_typ (cur_goal());
    revert ();
    set_abduction_variable ()

/// Wrapper around the tactic above
/// The constraint should be of the shape `squash (equiv lhs rhs)`
let canon_monoid (use_smt:bool) (carrier_t:term) (eq m:term) (pr pr_bind:term) : Tac unit =
  norm [iota; zeta];
  let t = cur_goal () in
  // removing top-level squash application
  let sq, rel_xy = collect_app_ref t in
  // unpacking the application of the equivalence relation (lhs `EQ?.eq eq` rhs)
  (match rel_xy with
   | [(rel_xy,_)] -> (
       let open FStar.List.Tot.Base in
       let rel, xy = collect_app_ref rel_xy in
       if (length xy >= 2)
       then (
         match index xy (length xy - 2) , index xy (length xy - 1) with
         | (lhs, Q_Explicit) , (rhs, Q_Explicit) ->
           canon_l_r use_smt carrier_t eq m pr pr_bind lhs rel rhs
         | _ -> fail "Goal should have been an application of a binary relation to 2 explicit arguments"
       )
       else (
         fail "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments"
       )
     )
   | _ -> fail "Goal should be squash applied to a binary relation")

/// Instantiation of the generic AC-unification tactic with the vprop commutative monoid
let canon' (use_smt:bool) (pr:term) (pr_bind:term) : Tac unit =
  canon_monoid use_smt (pack (Tv_FVar (pack_fv [`%vprop]))) (`req) (`rm) pr pr_bind

/// Counts the number of unification variables corresponding to vprops in the term [t]
let rec slterm_nbr_uvars (t:term) : Tac int =
  match inspect t with
  | Tv_Uvar _ _ -> 1
  | Tv_App _ _ ->
    let hd, args = collect_app t in
    if term_eq hd (`star) || term_eq hd (`VStar) || term_eq hd (`VUnit) then
      // Only count the number of unresolved slprops, not program implicits
      slterm_nbr_uvars_argv args
    else if is_uvar hd then 1
    else 0
  | Tv_Abs _ t -> slterm_nbr_uvars t
  | _ -> 0

and slterm_nbr_uvars_argv (args: list argv) : Tac int =
  fold_left (fun n (x, _) -> n + slterm_nbr_uvars x) 0 args

val solve_can_be_split_for (#a: Type u#b) : a -> Tot unit

val solve_can_be_split_lookup : unit // FIXME: src/reflection/FStar.Reflection.Basic.lookup_attr only supports fvar attributes, so we cannot directly look up for (solve_can_be_split_for blabla), we need a nullary attribute to use with lookup_attr

let rec dismiss_all_but_last' (l: list goal) : Tac unit =
  match l with 
  | [] | [_] -> set_goals l
  | _ :: q -> dismiss_all_but_last' q

let dismiss_all_but_last () : Tac unit =
  dismiss_all_but_last' (goals ())

let rec dismiss_non_squash_goals' (keep:list goal) (goals:list goal)
  : Tac unit
  = match goals with
    | [] -> set_goals (List.Tot.rev keep)
    | hd :: tl ->
     let f = term_as_formula' (goal_type hd) in
     match f with
     | App hs _ ->
       if hs `term_eq` (`squash) || hs `term_eq` (`auto_squash)
       then dismiss_non_squash_goals' (hd::keep) tl
       else dismiss_non_squash_goals' keep tl

     | _ ->
       dismiss_non_squash_goals' keep tl

let dismiss_non_squash_goals () =
  let g = goals () in
  dismiss_non_squash_goals' [] g

let rec term_mem (te: term) (l: list term) : Tot bool =
  match l with
  | [] -> false
  | t' :: q ->
    if te `term_eq` t' then true else term_mem te q

let rec lookup_by_term_attr' (attr: term) (e: env) (found: list fv) (l: list fv) : Tot (list fv)
  (decreases l)
=
  match l with
  | [] -> List.Tot.rev found
  | f :: q ->
    let n = inspect_fv f in
    begin match lookup_typ e n with
    | None -> lookup_by_term_attr' attr e found q
    | Some se ->
      let found' =
        if attr `term_mem` sigelt_attrs se
        then f :: found
        else found
      in
      lookup_by_term_attr' attr e found' q
    end

let lookup_by_term_attr (label_attr: term) (attr: term) : Tac (list fv) =
  let e = cur_env () in
  let candidates = lookup_attr label_attr e in
  lookup_by_term_attr' attr e [] candidates

let rec bring_last_goal_on_top' (others: list goal) (goals: list goal) : Tac unit =
  match goals with
  | [] -> set_goals (List.Tot.rev others)
  | last :: [] -> set_goals (last :: List.Tot.rev others)
  | a :: q -> bring_last_goal_on_top' (a :: others) q

let bring_last_goal_on_top () =
  let g = goals () in
  bring_last_goal_on_top' [] g

let rec extract_contexts
  (lemma_left lemma_right label_attr attr: term)
  (t: term)
: Tac (option (unit -> Tac unit))
=
  let hd, tl = collect_app t in
  if hd `term_eq` (`star) || hd `term_eq` (`VStar)
  then
    match tl with
    | (t_left, Q_Explicit) :: (t_right, Q_Explicit) :: [] ->
      let extract_right () : Tac (option (unit -> Tac unit)) =
        match extract_contexts lemma_left lemma_right label_attr attr t_right with
        | None -> None
        | Some f ->
          Some (fun _ ->
            apply_lemma lemma_right;
            dismiss_all_but_last ();
            f ()
          )
      in
      begin match extract_contexts lemma_left lemma_right label_attr attr t_left with
      | None -> extract_right ()
      | Some f ->
        Some (fun _ ->
          try
            apply_lemma lemma_left;
            dismiss_all_but_last ();
            f ()
          with _ ->
            begin match extract_right () with
            | None -> fail "no context on the right either"
            | Some g -> g ()
            end
        )
      end
    | _ -> None
  else
    let candidates = lookup_by_term_attr label_attr (mk_app attr [hd, Q_Explicit]) in
    if Nil? candidates
    then None
    else
      Some (fun _ ->
        first (List.Tot.map (fun candidate _ -> apply_lemma (Tv_FVar candidate) <: Tac unit) candidates);
        dismiss_non_squash_goals ()
      )

let extract_cbs_contexts = extract_contexts
  (`can_be_split_congr_l)
  (`can_be_split_congr_r)
  (`solve_can_be_split_lookup)
  (`solve_can_be_split_for)

let open_existentials () : Tac unit
  =
       let e = cur_env () in
       if Nil? (lookup_attr (`solve_can_be_split_lookup) e)
       then fail "Tactic disabled: no available lemmas in context";
       norm [delta_attr [`%__reduce__]];
       let t0 = cur_goal () in
       match collect_app t0 with
       | _ (* squash/auto_squash *) , (t1, Q_Explicit) :: [] ->
         let hd, tl = collect_app t1 in
         if hd `term_eq` (`can_be_split)
         then
           match tl with
           | _ (* lhs *) :: (rhs, Q_Explicit) :: [] ->
             begin match extract_cbs_contexts rhs with
             | None -> fail "open_existentials: no context found"
             | Some f ->
                 apply_lemma (`can_be_split_trans_rev);
                 dismiss_all_but_last ();
                 split ();
                 focus f;
                 bring_last_goal_on_top () // so that any preconditions for the selected lemma are scheduled for later
             end
           | _ -> fail "open_existentials: ill-formed can_be_split"
         else
           fail "open_existentials: not a can_be_split goal"
       | _ -> fail "open_existentials: not a squash goal"

let try_open_existentials () : Tac bool =
  focus (fun _ ->
    try
      open_existentials ();
      true
    with _ -> false
  )

(* Solving the can_be_split* constraints, if they are ready to be scheduled
   A constraint is deemed ready to be scheduled if it contains only one vprop unification variable
   If so, constraints are stripped to their underlying  definition based on vprop equivalence,
   introducing universally quantified variables when needed.
   Internal details of the encoding are removed through normalization, before calling the AC-unification
   tactic defined above
*)

/// Solves a `can_be_split` constraint
let rec solve_can_be_split (args:list argv) : Tac bool =
  match args with
  | [(t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        try
          focus (fun _ -> apply_lemma (`equiv_can_be_split);
                     dismiss_slprops();
                     // If we have exactly the same term on both side,
                     // equiv_sl_implies would solve the goal immediately
                     or_else (fun _ -> apply_lemma (`equiv_refl))
                      (fun _ ->
                      if rnbr = 0 then apply_lemma (`equiv_sym);

                       norm [delta_only [
                              `%__proj__CM__item__unit;
                              `%__proj__CM__item__mult;
                              `%rm;
                              `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                              `%fst; `%snd];
                            delta_attr [`%__reduce__];
                            primops; iota; zeta];
                       canon' false (`true_p) (`true_p)));
          true
        with
        | _ ->
          let opened_some = try_open_existentials () in
          if opened_some then solve_can_be_split args // we only need args for their number of uvars, which has not changed
          else false
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen

/// Solves a can_be_split_dep constraint
let solve_can_be_split_dep (args:list argv) : Tac bool =
  match args with
  | [(p, _); (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ ->
          let p_bind = implies_intro () in
          apply_lemma (`equiv_can_be_split);
          dismiss_slprops ();
          or_else
            (fun _ ->
              let b = unify p (`true_p) in
              if not b then fail "could not unify SMT prop with True";
              apply_lemma (`equiv_refl))
            (fun _ ->
              if lnbr <> 0 && rnbr = 0 then apply_lemma (`equiv_sym);
              or_else (fun _ ->  flip()) (fun _ -> ());
              norm [delta_only [
                     `%__proj__CM__item__unit;
                     `%__proj__CM__item__mult;
                     `%rm;
                     `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                     `%fst; `%snd];
                   delta_attr [`%__reduce__];
                   primops; iota; zeta];
              canon' true p p_bind));

        true

      ) else false

  | _ -> fail "ill-formed can_be_split_dep"

/// Helper rewriting lemma
val emp_unit_variant (p:vprop) : Lemma
   (ensures can_be_split p (p `star` emp))

/// Solves a can_be_split_forall constraint
let solve_can_be_split_forall (args:list argv) : Tac bool =
  match args with
  | [_; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ ->
          ignore (forall_intro());
          apply_lemma (`equiv_can_be_split);
          dismiss_slprops();
          or_else (fun _ -> apply_lemma (`equiv_refl))
            (fun _ ->
            if lnbr <> 0 && rnbr = 0 then apply_lemma (`equiv_sym);
            or_else (fun _ ->  flip()) (fun _ -> ());
            norm [delta_only [
                   `%__proj__CM__item__unit;
                   `%__proj__CM__item__mult;
                   `%rm;
                   `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                   `%fst; `%snd];
                delta_attr [`%__reduce__];
                 primops; iota; zeta];
            canon' false (`true_p) (`true_p)));
        true
      ) else false

  | _ -> fail "Ill-formed can_be_split_forall, should not happen"

val solve_can_be_split_forall_dep_for (#a: Type u#b) : a -> Tot unit

val solve_can_be_split_forall_dep_lookup : unit // FIXME: same as solve_can_be_split_for above

let extract_cbs_forall_dep_contexts
=
  extract_contexts
    (`can_be_split_forall_dep_congr_l)
    (`can_be_split_forall_dep_congr_r)
    (`solve_can_be_split_forall_dep_lookup)
    (`solve_can_be_split_forall_dep_for)

let open_existentials_forall_dep () : Tac unit
=
  let e = cur_env () in
  if Nil? (lookup_attr (`solve_can_be_split_forall_dep_lookup) e)
  then fail "Tactic disabled: no available lemmas in context";
  norm [
    delta_only [
    `%FStar.Algebra.CommMonoid.Equiv.__proj__CM__item__unit;
    `%FStar.Algebra.CommMonoid.Equiv.__proj__CM__item__mult;
    `%rm;
    ];
    iota;
    delta_attr [`%__reduce__];
  ];
  let t0 = cur_goal () in
  match collect_app t0 with
  | _ (* squash/auto_squash *) , (t1, Q_Explicit) :: [] ->
    let hd, tl = collect_app t1 in
    if hd `term_eq` (`can_be_split_forall_dep)
    then
      match tl with
      | _ (* cond *) :: _ (* lhs *) :: (rhs, Q_Explicit) :: []
      | (_, Q_Implicit) (* #a *) :: _ (* cond *) :: _ (* lhs *) :: (rhs, Q_Explicit) :: [] ->
        begin match inspect rhs with
        | Tv_Abs _ body ->
          begin match extract_cbs_forall_dep_contexts body with
          | None -> fail "open_existentials_forall_dep: no candidate"
          | Some f ->
            apply_lemma (`can_be_split_forall_dep_trans_rev);
            dismiss_all_but_last ();
            split ();
            focus f;
            bring_last_goal_on_top ();
            if Cons? (goals ()) then norm []
          end
        | _ -> fail "open_existentials_forall_dep : not an abstraction"
        end
      | _ -> fail "open_existentials_forall_dep : wrong number of arguments to can_be_split_forall_dep"
    else
      fail "open_existentials_forall_dep : not a can_be_split_forall_dep goal"
  | _ ->
    fail "open_existentials_forall_dep : not a squash/auto_squash goal"

let try_open_existentials_forall_dep () : Tac bool
=
  focus (fun _ ->
    try
      open_existentials_forall_dep ();
      true
    with _ -> false
  )

/// Solves a can_be_split_forall_dep constraint
let rec solve_can_be_split_forall_dep (args:list argv) : Tac bool =
  match args with
  | [_; (pr, _); (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        try
         focus (fun _ ->
          norm [];
          let x = forall_intro () in
          let pr = mk_app pr [(binder_to_term x, Q_Explicit)] in
          let p_bind = implies_intro () in
          apply_lemma (`equiv_can_be_split);
          or_else (fun _ -> flip()) (fun _ -> ());
          let pr = norm_term [] pr in
          or_else
            (fun _ ->
              let b = unify pr (`true_p) in
              if not b then fail "could not unify SMT prop with True";
              apply_lemma (`equiv_refl))
            (fun _ ->
              if lnbr <> 0 && rnbr = 0 then apply_lemma (`equiv_sym);
              or_else (fun _ ->  flip()) (fun _ -> ());
              norm [delta_only [
                     `%__proj__CM__item__unit;
                     `%__proj__CM__item__mult;
                     `%rm;
                     `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                     `%fst; `%snd];
                   delta_attr [`%__reduce__];
                   primops; iota; zeta];
              canon' true pr p_bind));

         true
       with
       | _ ->
         let opened = try_open_existentials_forall_dep () in
         if opened
         then solve_can_be_split_forall_dep args // we only need args for their number of uvars, which has not changed
         else false
      ) else false

  | _ -> fail "Ill-formed can_be_split_forall_dep, should not happen"

/// Solves an equiv_forall constraint
let solve_equiv_forall (args:list argv) : Tac bool =
  match args with
  | [_; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> apply_lemma (`equiv_forall_elim);
                      match goals () with
                      | [] -> ()
                      | _ ->
                        dismiss_slprops ();
                        ignore (forall_intro());
                        or_else
                          (fun _ -> apply_lemma (`equiv_refl))
                          (fun _ ->
                            if lnbr <> 0 && rnbr = 0 then apply_lemma (`equiv_sym);
                            or_else (fun _ ->  flip()) (fun _ -> ());
                            norm [delta_only [
                                    `%__proj__CM__item__unit;
                                    `%__proj__CM__item__mult;
                                    `%rm;
                                    `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                                    `%fst; `%snd];
                                  delta_attr [`%__reduce__];
                                  primops; iota; zeta];
                            canon' false (`true_p) (`true_p)));
        true
      ) else false

  | _ -> fail "Ill-formed equiv_forall, should not happen"

/// Solves an equiv constraint
let solve_equiv (args:list argv) : Tac bool =
  match args with
  | [(t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ ->
          or_else
            (fun _ -> apply_lemma (`equiv_refl))
            (fun _ ->
              if lnbr <> 0 && rnbr = 0 then apply_lemma (`equiv_sym);
              or_else (fun _ -> flip ()) (fun _ -> ());
              norm [delta_only [
                      `%__proj__CM__item__unit;
                      `%__proj__CM__item__mult;
                      `%rm;
                      `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                      `%fst; `%snd];
                    delta_attr [`%__reduce__];
                    primops; iota; zeta];
              canon' false (`true_p) (`true_p)));
        true

      ) else false

  | _ -> fail "Ill-formed equiv, should not happen"

/// Solves a can_be_split_post constraint
let solve_can_be_split_post (args:list argv) : Tac bool =
  match args with
  | [_; _; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> norm[];
                      let g = _cur_goal () in
                      ignore (forall_intro());
                      apply_lemma (`equiv_forall_elim);
                      match goals () with
                      | [] -> ()
                      | _ ->
                        dismiss_slprops ();
                        ignore (forall_intro());
                        or_else
                          (fun _ -> apply_lemma (`equiv_refl))
                          (fun _ ->
                            if lnbr <> 0 && rnbr = 0 then apply_lemma (`equiv_sym);
                            or_else (fun _ ->  flip()) (fun _ -> ());
                            norm [delta_only [
                                    `%__proj__CM__item__unit;
                                    `%__proj__CM__item__mult;
                                    `%rm;
                                    `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                                    `%fst; `%snd];
                                  delta_attr [`%__reduce__];
                                  primops; iota; zeta];
                            canon' false (`true_p) (`true_p)));
        true
      ) else false

  | _ -> fail "ill-formed can_be_split_post"

/// Checks whether any of the two terms was introduced during a Steel monadic return
let is_return_eq (l r:term) : Tac bool =
  let nl, al = collect_app l in
  let nr, ar = collect_app r in
  term_eq nl (`return_pre) || term_eq nr (`return_pre)

/// Solves indirection equalities introduced by the layered effects framework.
/// If these equalities were introduced during a monadic return, they need to be solved
/// at a later stage to avoid overly restricting contexts of unification variables
let rec solve_indirection_eqs (fuel: nat) : Tac unit =
  if fuel = 0
  then ()
  else match goals () with
  | [] -> ()
  | hd::_ ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
        if is_return_eq l r then later() else trefl();
        solve_indirection_eqs (fuel - 1)
    | _ -> later(); solve_indirection_eqs (fuel - 1)

/// Solve all equalities in the list of goals by calling the F* unifier
let rec solve_all_eqs (fuel: nat) : Tac unit =
  if fuel = 0
  then ()
  else match goals () with
  | [] -> ()
  | hd::_ ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
        trefl();
        solve_all_eqs (fuel - 1)
    | _ -> later(); solve_all_eqs (fuel - 1)

/// It is important to not normalize the return_pre eqs goals before unifying
/// See test7 in FramingTestSuite for a detailed explanation
let rec solve_return_eqs (fuel: nat) : Tac unit =
  if fuel = 0
  then ()
  else match goals () with
  | [] -> ()
  | hd::_ ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
        trefl();
        solve_return_eqs (fuel - 1)
    | _ -> later(); solve_return_eqs (fuel - 1)

/// Strip annotations in a goal, to get to the underlying slprop equivalence
let goal_to_equiv (loc:string) : Tac unit
  = let t = cur_goal () in
    let f = term_as_formula' t in
    match f with
    | App hd0 t ->
      if not (hd0 `term_eq` (`squash))
      then fail (loc ^ " unexpected non-squash goal in goal_to_equiv");
      let hd, args = collect_app t in
      if term_eq hd (`can_be_split) then (
        apply_lemma (`equiv_can_be_split)
      ) else if term_eq hd (`can_be_split_forall) then (
        ignore (forall_intro ());
        apply_lemma (`equiv_can_be_split)
      ) else if term_eq hd (`equiv_forall) then (
        apply_lemma (`equiv_forall_elim);
        ignore (forall_intro ())
      ) else if term_eq hd (`can_be_split_post) then (
        apply_lemma (`can_be_split_post_elim);
        dismiss_slprops();
        ignore (forall_intro ());
        ignore (forall_intro ())
      ) else if term_eq hd (`can_be_split_dep) then (
        fail ("can_be_split_dep not supported in " ^ loc)
      ) else if term_eq hd (`can_be_split_forall_dep) then (
        fail ("can_be_split_forall_dep not supported in " ^ loc)
      ) else
        // This should never happen
        fail (loc ^ " goal in unexpected position")
    | _ -> fail (loc ^ " unexpected goal")

let rec term_dict_assoc
  (#a: Type)
  (key: term)
  (l: list (term & a))
: Tac (list a)
= match l with
  | [] -> []
  | (k, v) :: q ->
    let q' = term_dict_assoc key q in
    if k `term_eq` key
    then (v :: q')
    else q'

/// Returns true if the goal has been solved, false if it should be delayed
let solve_or_delay (dict: list (term & (unit -> Tac bool))) : Tac bool =
  // Beta-reduce the goal first if possible
  norm [];
  let f = term_as_formula' (cur_goal ()) in
  match f with
  | App hd0 t ->
    if hd0 `term_eq` (`squash)
    then
      let hd, args = collect_app t in
      if term_eq hd (`can_be_split) then solve_can_be_split args
      else if term_eq hd (`can_be_split_forall) then solve_can_be_split_forall args
      else if term_eq hd (`equiv_forall) then solve_equiv_forall args
      else if term_eq hd (`can_be_split_post) then solve_can_be_split_post args
      else if term_eq hd (`equiv) then solve_equiv args
      else if term_eq hd (`can_be_split_dep) then solve_can_be_split_dep args
      else if term_eq hd (`can_be_split_forall_dep) then solve_can_be_split_forall_dep args
      else
        let candidates = term_dict_assoc hd dict in
        let run_tac (tac: unit -> Tac bool) () : Tac bool =
          focus tac
        in
        begin try
          first (List.Tot.map run_tac candidates)
        with _ ->
          (* this is a logical goal, solve it only if it has no uvars *)
          if List.Tot.length (FStar.Reflection.Builtins.free_uvars t) = 0
          then (smt (); true)
          else false
        end
    else
      // TODO: handle non-squash goals here
      false
  | Comp (Eq _) l r ->
    let lnbr = List.Tot.length (FStar.Reflection.Builtins.free_uvars l) in
    let rnbr = List.Tot.length (FStar.Reflection.Builtins.free_uvars r) in
    // Only solve equality if one of the terms is completely determined
    if lnbr = 0 || rnbr = 0 then (trefl (); true) else false
  | _ -> false

/// Returns true if it successfully solved a goal
/// If it returns false, it means it didn't find any solvable goal,
/// which should mean only delayed goals are left
let rec pick_next (dict: _) (fuel: nat) : Tac bool =
  if fuel = 0
  then false
  else match goals () with
  | [] -> true
  | _::_ -> if solve_or_delay dict then true else (later (); pick_next dict (fuel - 1))

/// Main loop to schedule solving of goals.
/// The goals () function fetches all current goals in the context
let rec resolve_tac (dict: _) : Tac unit =
  match goals () with
  | [] -> ()
  | g ->
    norm [];
    // TODO: If it picks a goal it cannot solve yet, try all the other ones?
    if pick_next dict (List.Tot.length g) then resolve_tac dict
    else fail "Could not make progress, no solvable goal found"

/// Special case for logical requires/ensures goals, which correspond only to equalities
let rec resolve_tac_logical (dict: _) : Tac unit =
  match goals () with
  | [] -> ()
  | g ->
    let fuel = List.Tot.length g in
    if pick_next dict fuel then resolve_tac_logical dict
    else
      // This is only for requires/ensures constraints, which are equalities
      // There should always be a scheduling of constraints, but it can happen
      // that some uvar for the type of an equality is not resolved.
      // If we reach this point, we try to simply call the unifier instead of failing directly
      solve_all_eqs fuel

/// Determining whether the type represented by term [t] corresponds to one of the logical (requires/ensures) goals
let typ_contains_req_ens (t:term) : Tac bool =
  let name, _ = collect_app t in
  if term_eq name (`req_t) ||
     term_eq name (`ens_t) ||
     term_eq name (`pure_wp) ||
     term_eq name (`pure_pre) ||
     term_eq name (`pure_post)
  then true
  else false

/// Splits goals between separation logic goals (slgoals) and requires/ensures goals (loggoals)
let rec filter_goals (l:list goal) : Tac (list goal * list goal) =
  match l with
  | [] -> [], []
  | hd::tl ->
      let slgoals, loggoals = filter_goals tl in
      match term_as_formula' (goal_type hd) with
      | Comp (Eq t) _ _ ->
        if Some? t then
          let b = typ_contains_req_ens (Some?.v t) in
          if b then (
            slgoals, hd::loggoals
          )
          else (
            hd::slgoals, loggoals
          )
        else (
          hd::slgoals, loggoals
        )
      | App t _ -> if term_eq t (`squash) then hd::slgoals, loggoals else slgoals, loggoals
      | _ -> slgoals, loggoals

let is_true (t:term) () : Tac unit =
  match term_as_formula t with
  | True_ -> exact (`())
  | _ -> raise Goal_not_trivial

/// Solve the maybe_emp goals:
/// Normalize to unfold maybe_emp(_dep) and the reduce the if/then/else, and
/// solve the goal (either an equality through trefl, or True through trivial)
let rec solve_maybe_emps (fuel: nat) : Tac unit =
  if fuel = 0
  then ()
  else match goals () with
  | [] -> ()
  | _::_ ->
    let f = term_as_formula' (cur_goal ()) in (
    match f with
    | App hd0 t ->
      if not (hd0 `term_eq` (`squash))
      then later ()
      else
        let hd, args = collect_app t in
        if term_eq hd (`maybe_emp) then
          (norm [delta_only [`%maybe_emp]; iota; zeta; primops; simplify];
          let g = cur_goal () in
          or_else (is_true g) trefl)
        else if term_eq hd (`maybe_emp_dep) then
          (norm [delta_only [`%maybe_emp_dep]; iota; zeta; primops; simplify];
          let g = cur_goal () in
          or_else (is_true g) (fun _ -> ignore (forall_intro ()); trefl ()))
        else later()
    | _ -> later()
    );
    solve_maybe_emps (fuel - 1)

/// Normalizes all the return_pre annotations once they are not needed anymore
let rec norm_return_pre (fuel: nat) : Tac unit =
  if fuel = 0
  then ()
  else match goals () with
  | [] -> ()
  | _::_ -> norm [delta_only [`%return_pre]]; later(); norm_return_pre (fuel - 1)

let print_goal (g:goal) =
  let t = goal_type g in
  term_to_string t

let print_goals (g:list goal) =
  let strs = List.Tot.map print_goal g in
  String.concat "\n" strs

/// The entry point of the frame inference tactic:
/// The resolve_implicits; framing_implicit annotation indicates that this tactic should
/// be called by the F* typechecker to solve all implicits annotated with the `framing_implicit` attribute.
/// The `plugin` attribute ensures that this tactic is compiled, and executed natively for performance reasons

let init_resolve_tac' (dict: _) : Tac unit =
  // We split goals between framing goals, about slprops (slgs)
  // and goals related to requires/ensures, that depend on slprops (loggs)
  let slgs, loggs = filter_goals (goals()) in
  // print ("SL Goals: \n" ^ print_goals slgs);
  // print ("Logical goals: \n" ^ print_goals loggs);

  // We first solve the slprops
  set_goals slgs;

  // We solve all the maybe_emp goals first: All "extra" frames are directly set to emp
  solve_maybe_emps (List.Tot.length (goals ()));

  // We first solve all indirection equalities that will not lead to imprecise unification
  // i.e. we can solve all equalities inserted by layered effects, except the ones corresponding
  // to the preconditions of a pure return
  solve_indirection_eqs (List.Tot.length (goals()));

  // To debug, it is best to look at the goals at this stage. Uncomment the next line
  // dump "initial goals";

  // We can now solve the equalities for returns
  solve_return_eqs (List.Tot.length (goals()));

  // It is important to not normalize the return_pre equalities before solving them
  // Else, we lose some variables dependencies, leading to the tactic being stuck
  // See test7 in FramingTestSuite for more explanations of what is failing
  // Once unification has been done, we can then safely normalize and remove all return_pre
  norm_return_pre (List.Tot.length (goals()));

  // Finally running the core of the tactic, scheduling and solving goals
  resolve_tac dict;

  // We now solve the requires/ensures goals, which are all equalities
  // All slprops are resolved by now
  set_goals loggs;

  resolve_tac_logical dict

// [@@ resolve_implicits; framing_implicit]
[@@ plugin]
let init_resolve_tac () : Tac unit = init_resolve_tac' []

(* AF: There probably is a simpler way to get from p to squash p in a tactic, so that we can use apply_lemma *)
let squash_and p (x:squash (p /\ True)) : (p /\ True) =
  let x : squash (p `Prims.pair` True) = FStar.Squash.join_squash x in
  x

/// Calling into the framing tactic to ensure that the vprop whose selector we are trying to access is in the context
[@@plugin]
let selector_tactic () : Tac unit =
  apply (`squash_and);
  apply_lemma (`intro_can_be_split_frame);
  flip ();
  norm [delta_only [
         `%CE.__proj__CM__item__unit;
         `%CE.__proj__CM__item__mult;
         `%rm;
         `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
         `%fst; `%snd];
       delta_attr [`%__reduce__];
       primops; iota; zeta];
  canon' false (`true_p) (`true_p)

/// Specific tactic used during the SteelAtomicBase and SteelBase effect definitions:
/// This allows us to write more complex if_then_else combinators, while proving them
/// sound with respect to subcomp
[@@ resolve_implicits; ite_attr]
let ite_soundness_tac () : Tac unit =
  let slgs, loggoals = filter_goals (goals ()) in
  set_goals slgs;
  solve_indirection_eqs (List.Tot.length slgs);
  // This is the actual subcomp goal. We can only solve it
  // once all uvars are solved
  let subcomp_goal = _cur_goal () in
  match goals () with
  | [] -> fail "should not happen"
  | _::tl -> set_goals tl;

  or_else (fun _ -> apply_lemma (`equiv_forall_refl)) assumption;
  or_else (fun _ ->
    or_else (fun _ -> apply_lemma (`can_be_split_dep_refl))
            (fun _ -> apply_lemma (`can_be_split_refl)) // Different formalism in Steel.ST
    ) assumption;

  // Discharging the maybe_emp by SMT
  smt ();
  // Now propagating all equalities for the requires/ensures
  set_goals loggoals;
  resolve_tac_logical [];
  // Now taking care of the actual subcomp VC
  set_goals [subcomp_goal];
  norm [];
  // We remove the with_tactic call with executing the tactic before calling the SMT.
  split ();
  // Remove the `rewrite_by_tactic` nodes
  pointwise' (fun _ -> or_else
    (fun _ -> apply_lemma (`unfold_rewrite_with_tactic))
    trefl);
  smt ()


/// Normalization step for VC generation, used in Steel and SteelAtomic subcomps
/// This tactic is executed after frame inference, and just before sending the query to the SMT
/// As such, it is a good place to add debugging features to inspect SMT queries when needed
let vc_norm () : Tac unit = norm normal_steps; trefl()

////////////////////////////////////////////////////////////////////////////////
//Common datatypes for the atomic & ghost effects
////////////////////////////////////////////////////////////////////////////////

/// A datatype indicating whether a computation is ghost (unobservable) or not
type observability : eqtype =
  | Observable
  | Unobservable

(* Helpers to handle observability inside atomic computations *)

unfold
let obs_at_most_one (o1 o2:observability) =
  o1=Unobservable || o2=Unobservable

unfold
let join_obs (o1:observability) (o2:observability) =
  if o1 = Observable || o2 = Observable
  then Observable
  else Unobservable

(* Lifting invariants to vprops *)

///  This operator asserts that the logical content of invariant [i] is the separation logic
///  predicate [p]
noextract
let ( >--> ) (i:iname) (p:vprop) : prop = i >--> (hp_of p)

/// [i : inv p] is an invariant whose content is [p]
let inv (p:vprop) = i:Ghost.erased iname{reveal i >--> p}

/// Ghost check to determing whether invariant [i] belongs to the set of opened invariants [e]
let mem_inv (#p:vprop) (e:inames) (i:inv p) : erased bool = elift2 (fun e i -> Set.mem i e) e i

/// Adding invariant [i] to the set of opened invariants [e]
noextract
let add_inv (#p:vprop) (e:inames) (i:inv p) : inames =
  Set.union (Set.singleton (reveal i)) (reveal e)

noextract
let set_add i o : inames = Set.union (Set.singleton i) o
