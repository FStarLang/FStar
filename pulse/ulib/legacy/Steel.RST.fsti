(*
   Copyright 2008-2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governig permissions and
   limitations under the License.
*)
module Steel.RST

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module A = LowStar.Array

include Steel.Resource

/// The `RST` effect is the top concept of the Steel framework. It offers a way of specifying
/// function in terms of resources, abstracting away the `modifies` theory of `LowStar.Array`.

(****
  Abstract modifies clause for the resource-indexed
  state effect
*)

/// Because this new state effect will only talk about heap modifications structured in terms of
/// resources, we can refine the notion of `modifies`. More precisely, if `l1` is modified into `l2`
/// when going from heap `h0` to heap `h1`, then every other used region of the heap stays disjoint
/// from the modifies region and stays used. It morally means that any growth in the modified region
/// induced by a function does not touch existing used locations.

let frame_usedness_preservation (l1 l2:A.loc) (h0 h1:HS.mem) = forall (frame: A.loc).
 (A.loc_disjoint frame l1 /\ A.loc_includes (A.loc_used_in h0) frame) ==>
   (A.loc_disjoint frame l2 /\ A.loc_includes (A.loc_used_in h1) frame)

val frame_usedness_preservation_intro (l1 l2: A.loc) (h0 h1:HS.mem)
  (lemma: (frame: A.loc) -> Lemma
    (requires ((A.loc_disjoint frame l1) /\ A.loc_includes (A.loc_used_in h0) frame))
    (ensures (A.loc_disjoint frame l2 /\ A.loc_includes (A.loc_used_in h1) frame))
  )
  : Lemma (frame_usedness_preservation l1 l2 h0 h1)

val frame_usedness_preservation_elim (l1 l2: A.loc) (h0 h1:HS.mem) (frame: A.loc)
  : Lemma
    (requires (
      frame_usedness_preservation l1 l2 h0 h1 /\ (A.loc_disjoint frame l1) /\
      A.loc_includes (A.loc_used_in h0) frame)
    )
    (ensures (A.loc_disjoint frame l2 /\ A.loc_includes (A.loc_used_in h1) frame))

/// We can now define our new `modifies` in terms of resources.

val modifies (res0 res1:resource) (h0 h1:HS.mem) : prop

val reveal_modifies (_ : unit)
  : Lemma (forall res0 res1 h0 h1.{:pattern modifies res0 res1 h0 h1}
    modifies res0 res1 h0 h1 <==>
      A.modifies (as_loc (fp_of res0) h0) h0 h1 /\
      frame_usedness_preservation (as_loc (fp_of res0) h0) (as_loc (fp_of res1) h1) h0 h1
   )

val modifies_refl (res:resource) (h:HS.mem)
  : Lemma (modifies res res h h)
  [SMTPat (modifies res res h h)]

val modifies_trans (res0 res1 res2:resource) (h0 h1 h2:HS.mem)
  : Lemma
    (requires (modifies res0 res1 h0 h1 /\ modifies res1 res2 h1 h2))
    (ensures (modifies res0 res2 h0 h2))
  [SMTPat (modifies res0 res2 h0 h2); SMTPat (modifies res0 res1 h0 h1)]

(**** Subresources *)

/// `LowStar.Resource` defines `can_be_split_into`, but we need here an existential predicate to not
/// carry around all the splitting deltas.

val is_subresource_of (r0 r: resource) : Type0

val is_subresource_of_elim
  (r0 r: resource)
  (goal: Type)
  (lemma: (r1: resource) -> Lemma (requires (r `can_be_split_into` (r0 , r1))) (ensures goal))
  : Lemma
    (requires (r0 `is_subresource_of` r))
    (ensures goal)

val can_be_split_into_intro_star (r0 r1: resource)
  : Lemma
    (requires (True))
    (ensures ((r0 <*> r1) `can_be_split_into` (r0, r1)))
  [SMTPat (r0 <*> r1)]

val is_subresource_of_intro1 (r0 r r1: resource)
  : Lemma
    (requires (r `can_be_split_into` (r0, r1)))
    (ensures (r0 `is_subresource_of` r))
  [SMTPat (r `can_be_split_into` (r0, r1)); SMTPat (r0 `is_subresource_of` r)]

val is_subresource_of_intro2 (r0 r r1: resource)
  : Lemma
    (requires (r `can_be_split_into` (r1, r0)))
    (ensures (r0 `is_subresource_of` r))
  [SMTPat (r `can_be_split_into` (r1, r0)); SMTPat (r0 `is_subresource_of` r)]

val is_subresource_of_trans (r1 r2 r3: resource)
  : Lemma
    (requires (r1 `is_subresource_of` r2 /\ r2 `is_subresource_of` r3))
    (ensures (r1 `is_subresource_of` r3))
  [SMTPat (r1 `is_subresource_of` r2); SMTPat (r2 `is_subresource_of` r3);
   SMTPat (r1 `is_subresource_of` r3)]

val is_subresource_of_refl (r: resource) : Lemma(r `is_subresource_of` r)
  [SMTPat (r `is_subresource_of` r)]

open Steel.Tactics

#push-options "--no_tactics"

let subresource_intro_by_tactic
  (r0 r: resource)
  (#[resolve_subresource ()] delta: resource{squash (
    FStar.Tactics.with_tactic check_subresource (squash (r `can_be_split_into` (r0, delta)))
  )})
  (_ : unit)
  : Lemma (r0 `is_subresource_of` r)
  =
  FStar.Tactics.by_tactic_seman check_subresource (squash (r `can_be_split_into` (r0, delta)));
  is_subresource_of_intro1 r0 r delta

#pop-options

(**** Selectors *)

/// The spirit of `LowStar.Resource` is to limit our reasonning to a fragment of the heap. For the
/// `RST` effect, we push this idea further and we will no longer allow to speak about the entirety
/// of the heap inside pre and postconditions. Rather, we want to be only able to talk about the
/// resources at hand.

module Fext =  FStar.FunctionalExtensionality

/// We extend on the `LowStar.Resource.sel_t` selector type by allowing our new selectors to also
/// talk about the subresources contained inside the enclosing resource. Selectors are morally
/// `(r0:resource{r0 is_subresource_of r}) -> r0.t`, but we need to define them with functional
/// extensionality. Since selectors are morally a heap restricted to a resource, we call them rmem.

let rmem (r: resource) : Type =
  Fext.restricted_g_t (r0:resource{r0 `is_subresource_of` r}) (fun r0 -> r0.t)

/// The main way to make a selector is to derive one from a particular state of the heap.
/// `mk_rmem r h` effectively restricts your access to the heap to accesses that are valid and
/// within the resource you consider.

val mk_rmem
  (r: resource)
  (h: imem (inv_of r)) :
  Tot (rh:rmem r{
    forall (r0:resource{r0 `is_subresource_of` r}). {:pattern (rh r0) \/ (sel_of r0.view h) }
    rh r0 == sel_of r0.view h
  })


/// The only other transformation allowed on selectors is focusing on a subresource.

val focus_rmem (#r: resource) (h: rmem r) (r0: resource{r0 `is_subresource_of` r})
  : Tot (h':rmem r0{forall (arg: resource{arg `is_subresource_of` r0}).
    {:pattern (h' arg) \/ (h arg)}
    arg `is_subresource_of` r /\ h' arg == h arg
  })

/// In the ST state, pre and postconditions depended on the entire heap. Here, theses conditions
/// depend only on a `rmem` for the resource at hand (derived from a heap state).

let rprop r = rmem r -> Type0

/// `extend_rprop` is the dual of `focus_rmem`.

val extend_rprop (#r0: resource) (p: rprop r0) (r: resource{r0 `is_subresource_of` r})
  : Tot (rprop r)


(**** The RST effect *)

/// On top of the invariants of the resource at hand, we add another global invariant governing how
/// resources are used : the footprint of resources used in Steel functions have to be used.

val rst_inv (res:resource) (h:HS.mem) : GTot prop

val reveal_rst_inv (_ : unit)
  : Lemma (forall res h .
    rst_inv res h <==>
      A.loc_includes (A.loc_used_in h) (as_loc (fp_of res) h)
  )

val rst_inv_star (res0 res1: resource) (h: HS.mem)
  : Lemma (rst_inv (res0 <*> res1) h <==> rst_inv (res1 <*> res0) h)
  [SMTPat (rst_inv (res0 <*> res1) h)]


/// Finally, the RST effect. Eventually with the layered effects, its definition will be hidden
/// here. It has five indexes:
///
/// * the return type;
/// * the initial resource, which is the composite heap object formed by all the arguments to the
///   function;
/// * the final resource, which is the composite heap object alive at then end of the function
///   (and depends on the return value);
/// * the precondition, which is an `rprop` of the initial resource and should be used to indicate
///   the functional specification of the function, since all of the memory shape specification has
///   been dealt with in the two previous indexes;
/// * the postcondition, function of the initial and final resources selectors and the return
///   value.
///
/// The pre/postcondition of the `ST` effect have been split in two. First, you specify what happens
/// to the memory: what heap objects are live at the beginning, how the function transforms this
/// memory shape. Then, you can add traditionnal functional specification but, thanks to selectors,
/// these functional specification can only depend on the views of the resources you're handling.

let r_pre (res:resource) = rprop res
let r_post (a: Type) (res1: a -> resource) = x:a -> rprop (res1 x)

type rst_wp' (a:Type) (r_in:resource) (r_out:a -> resource) = r_post a r_out -> r_pre r_in

let rst_wp_monotonic
  (a:Type)
  (r_in:resource)
  (r_out:a -> resource)
  (wp:rst_wp' a r_in r_out) =
  forall (p q:r_post a r_out). (forall x h. p x h ==> q x h) ==> (forall h. wp p h ==> wp q h)

type rst_wp (a:Type) (r_in:resource) (r_out:a -> resource) =
  wp:rst_wp' a r_in r_out{rst_wp_monotonic a r_in r_out wp}


type repr (a:Type) (r_in:resource) (r_out:a -> resource) (wp:rst_wp a r_in r_out) =
  unit -> ST.STATE a
    (fun p h0 ->
      inv_of r_in h0 /\ rst_inv r_in h0 /\
      wp (fun (x:a) (h_r_out:rmem (r_out x)) ->
        forall (h1 : imem (inv_of (r_out x))). (
	    mk_rmem (r_out x) h1 == h_r_out /\
            inv_of (r_out x) h1 /\
            rst_inv (r_out x) h1 /\
            modifies r_in (r_out x) h0 h1
	  ) ==> p x h1
	) (mk_rmem r_in h0)
    )

inline_for_extraction
val returnc
  (a:Type)
  (x:a)
  (r:a -> resource)
  : repr a (r x) r (fun (p:r_post a r) h -> p x h)

inline_for_extraction
val bind (a:Type) (b:Type)
  (r_in_f:resource) (r_out_f:a -> resource) (wp_f:rst_wp a r_in_f r_out_f)
  (r_out_g:b -> resource) (wp_g:(x:a -> rst_wp b (r_out_f x) r_out_g))
  (f:repr a r_in_f r_out_f wp_f)
  (g:(x:a -> repr b (r_out_f x) r_out_g (wp_g x)))
  : repr b r_in_f r_out_g (fun p -> wp_f (fun x -> (wp_g x) p))

val subcomp (a:Type)
  (r_in:resource) (r_out:a -> resource)
  (wp_f:rst_wp a r_in r_out)
  (wp_g:rst_wp a r_in r_out)
  (f:repr a r_in r_out wp_f)
: Pure (repr a r_in r_out wp_g)
  (requires (forall p h. wp_g p h ==> wp_f p h))
  (ensures fun _ -> True)

let if_then_else (a:Type)
  (r_in:resource) (r_out:a -> resource)
  (wp_f:rst_wp a r_in r_out) (wp_g:rst_wp a r_in r_out)
  (f:repr a r_in r_out wp_f) (g:repr a r_in r_out wp_g)
  (p:Type0)
: Type =
  repr a r_in r_out
    (fun post h -> (p ==> wp_f post h) /\ ((~ p) ==> wp_g post h))

reifiable reflectable
layered_effect {
  RSTATE : a:Type -> r_in:resource -> r_out:(a -> resource) -> wp:rst_wp a r_in r_out -> Effect
  with repr         = repr;
       return       = returnc;
       bind         = bind;
       subcomp     = subcomp;
       if_then_else  = if_then_else
}


let return (#a:Type)
  (#r:a -> resource)
  (x:a)
: RSTATE a (r x) r (fun (p:r_post a r) h -> p x h)
= RSTATE?.reflect (returnc a x r)


/// Since RST wps are monotonic, we need monotonicity of PURE for lifts to typecheck
assume Pure_wp_monotonicity:
  forall (a:Type) (wp:pure_wp a).
    (forall (p q:pure_post a).
       (forall (x:a). p x ==> q x) ==>
       (wp p ==> wp q))

val lift_div_rstate (a:Type) (wp:pure_wp a) (r:resource) (f:unit -> DIV a wp)
: repr a r (fun _ -> r) (fun p h -> wp (fun x -> p x h))

sub_effect DIV ~> RSTATE = lift_div_rstate


/// Hoare style encoding

unfold
let hoare_to_wp
  (a: Type)
  (r_in: resource)
  (r_out: a -> resource)
  (pre: r_pre r_in)
  (post: rmem r_in -> (x:a) -> rprop (r_out x)) : r_post a r_out -> rmem r_in -> Type
  = fun (p:r_post a r_out) (h0:rmem r_in) ->
    pre h0 /\ (forall (x:a) (h1:rmem (r_out x)). post h0 x h1 ==> p x h1)

effect RST (a:Type)
  (r_in:resource) (r_out:a -> resource)
  (pre:rprop r_in) (post:rmem r_in -> (x:a) -> rprop (r_out x))
= RSTATE a r_in r_out (hoare_to_wp a r_in r_out pre post)

unfold
let rst_repr
  (a: Type)
  (r_in:resource)
  (r_out:a -> resource)
  (pre:rprop r_in)
  (post:rmem r_in -> (x:a) -> rprop (r_out x)) =
  repr a r_in r_out (hoare_to_wp a r_in r_out pre post)

/// Similar to `FStar.Hyperstack.ST.get`, this helper gives you a rmem based on the current state of
/// the heap

val get (r: resource) : RST (rmem r)
  r
  (fun _ -> r)
  (fun _ -> True)
  (fun h0 h h1 -> h == h0 /\ h0 == h1)


(**** The frame rule *)

#push-options "--no_tactics"

/// Finally, the workhorse separation logic rule that will be pervasive in Steel programs: the frame
/// rule. All calls to RST functions should be encapsulated inside `rst_frame`. The rule takes 3
/// mandatory arguments:
///
/// * `outer0` is the resource summming up all the live heap objects when the function `f` is
///   called;
/// * `outer1 x` is the resource summing up all the live heap objects after the function `f`
///   returns with return value `x`;
/// * `f` is the RST function you want to call, with pre and post resources `inner0` and
///   `outer1 x`.
///
/// Morally, you want to call `f` on `inner0` which is a fraction of your `outer0` resource context.
/// What this rule does is to find automatically (thanks to a tactic) the `delta` such that
/// `outer0 == inner0 <*> delta`. Then it checks that the `outer1 x` you provided does indeed
/// satisfy `outer1 x == inner1 x <*> delta`. The postcondition of `f` is propagated to `outer1`,
/// as well as the core information provided by the frame rule: the `delta` does not change.

inline_for_extraction noextract val rst_frame
  (outer0:resource)
  (#inner0:resource)
  (#a:Type)
  (outer1:a -> resource)
  (#inner1:a -> resource)
  (#[resolve_delta ()]
     delta:resource{
       FStar.Tactics.with_tactic
         resolve_frame_delta
         (frame_delta outer0 inner0 outer1 inner1 delta)
     }
   )
  (#pre:rprop inner0)
  (#post:rmem inner0 -> (x:a) -> rprop (inner1 x))
   ($f:unit -> RST a inner0 inner1 pre post)
  : RST a outer0 outer1
    (FStar.Tactics.by_tactic_seman resolve_frame_delta
      (frame_delta outer0 inner0 outer1 inner1 delta);
      fun h ->
        pre (focus_rmem h inner0)
    )
    (reveal_can_be_split_into ();
      fun h0 x h1 ->
        post
          (focus_rmem h0 inner0)
          x
          (focus_rmem h1 (inner1 x)) /\
        (focus_rmem h0 delta == focus_rmem h1 delta)
    )

#pop-options

(**** Resource subtyping *)

/// Thanks to selectors, we can define abstract resource refinements that strenghten the invariant
/// of a resource.

val refine_inv (r:resource) (p:rprop r) : Tot (r':resource{
    r'.t == r.t /\
    r'.view == {r.view with inv = fun h -> (inv_of r) h /\ p (mk_rmem r h)}
  })

val cast_to_refined_inv (r: resource) (p:rprop r) : RST unit
  r
  (fun _ -> refine_inv r p)
  (fun h -> p h)
  (fun _ _ _ -> True)

val cast_from_refined_inv (r: resource) (p:rprop r) : RST unit
  (refine_inv r p)
  (fun _ -> r)
  (fun _ -> True)
  (fun _ _ h1 -> p h1)

val refine_view (r: resource) (#a: Type) (f: r.t -> GTot a) : GTot (r':resource{
    r'.t == a /\
    r'.view.fp == r.view.fp /\
    r'.view.inv == r.view.inv /\
    r'.view.sel == Fext.on_dom_g HS.mem (fun h -> f (r.view.sel h))
  })

val cast_to_refined_view (r: resource) (#a: Type)  (f: r.t -> GTot a) : RST unit
  r
  (fun _ -> refine_view r f)
  (fun _ -> True)
  (fun h0 _ h1 -> h1 (refine_view r f) == f (h0 r))
