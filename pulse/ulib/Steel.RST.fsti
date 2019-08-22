(*
   Copyright 2008-2019 Microsoft Research

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
      A.modifies (as_loc (fp res0) h0) h0 h1 /\
      frame_usedness_preservation (as_loc (fp res0) h0) (as_loc (fp res1) h1) h0 h1
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
  (h: imem (inv r)) :
  Tot (rh:rmem r{forall (r0:resource{r0 `is_subresource_of` r}). rh r0 == sel r0.view h})

/// The only other transformation allowed on selectors is focusing on a subresource.
val focus_rmem (#r: resource) (h: rmem r) (r0: resource{r0 `is_subresource_of` r})
  : Tot (rmem r0)

val focus_rmem_equality (outer inner: resource) (h: rmem outer) : Lemma
  (requires (inner `is_subresource_of` outer))
  (ensures (let focused = focus_rmem h inner in
    forall (arg:resource{arg `is_subresource_of` inner}). {:pattern focused arg; h arg} focused arg == h arg
  ))
  [SMTPat (focus_rmem #outer h inner)]

val focus_mk_rmem_equality (outer inner: resource) (h: HS.mem)
  : Lemma
    (requires (inv outer h /\ inner `is_subresource_of` outer))
    (ensures (is_subresource_of_elim inner outer (inv inner h) (fun _ -> ());
      focus_rmem (mk_rmem outer h) inner == mk_rmem inner h))

/// In the ST state, pre and postconditions depended on the entire heap. Here, theses conditions
/// depend only on a `rmem` for the resource at hand (derived from a heap state).
let rprop r = rmem r -> Type0

/// `extend_rprop` is the dual of `focus_rmem`.
val extend_rprop (#r0: resource) (p: rprop r0) (r: resource{r0 `is_subresource_of` r})
  : Tot (rprop r)

/// Thanks to selectors, we can define abstract resource refinements that strenghten the invariant
/// of a resource.
val hsrefine (r:resource) (p:rprop r) : Tot (r':resource{
    r'.t == r.t /\
    r'.view == {r.view with inv = fun h -> r.view.inv h /\ p (mk_rmem r h)}
  })

(**** The RST effect *)

/// On top of the invariants of the resource at hand, we add another global invariant governing how
/// resources are used : the footprint of resources used in Steel functions have to be used.
val rst_inv (res:resource) (h:HS.mem) : GTot prop

val reveal_rst_inv (_ : unit)
  : Lemma (forall res h .
    rst_inv res h <==>
      A.loc_includes (A.loc_used_in h) (as_loc (fp res) h)
  )

val rst_inv_star (res0 res1: resource) (h: HS.mem)
  : Lemma (rst_inv (res0 <*> res1) h <==> rst_inv (res1 <*> res0) h)
  [SMTPat (rst_inv (res0 <*> res1) h)]

let r_pre (res:resource) =  rprop res
let r_post
  (res0: resource)
  (a: Type)
  (res1: a -> resource) =
  rmem res0 -> x:a -> rprop (res1 x)


/// Finally, the RST effect. Eventually with the layered effects, its definition will be hidden
/// here. It has five indexes:
///  * the return type;
///  * the initial resource, which is the composite heap object formed by all the arguments to the
///    function;
///  * the final resource, which is the composite heap object alive at then end of the function
///    (and depends on the return value);
///  * the precondition, which is an `rprop` of the initial resource and should be used to indicate
///    the functional specification of the function, since all of the memory shape specification has
///    been dealt with in the two previous indexes;
///  * the postcondition, function of the initial and final resources selectors and the return
///    value.
/// The pre/postcondition of the `ST` effect have been split in two. First, you specify what happens
/// to the memory: what heap objects are live at the beginning, how the function transforms this
/// memory shape. Then, you can add traditionnal functional specification but, thanks to selectors,
/// these functional specification can only depend on the views of the resources you're handling.
effect RST
  (a: Type)
  (res0: resource)
  (res1: a -> resource)
  (pre: rprop res0)
  (post: rmem res0 -> (x:a) -> rprop (res1 x))
= ST.ST
  a
  (fun h0 -> inv res0 h0 /\ rst_inv res0 h0 /\ pre (mk_rmem res0 h0))
  (fun h0 x h1 ->
    inv res0 h0 /\ rst_inv res0 h0 /\ pre (mk_rmem res0 h0) /\
    inv (res1 x) h1 /\
    rst_inv (res1 x) h1 /\
    modifies res0 (res1 x) h0 h1 /\
    post (mk_rmem res0 h0) x (mk_rmem (res1 x) h1)
  )

/// Similar to `FStar.Hyperstack.ST.get`, this helper gives you a rmem based on the current state of
/// the heap
val get (r: resource) : RST
  (rmem r)
  (r)
  (fun _ -> r)
  (fun _ -> True)
  (fun h0 h h1 -> h == h0 /\ h0 == h1)


(**** The frame rule *)

open Steel.Tactics

#reset-options "--no_tactics"

/// Finally, the workhorse separation logic rule that will be pervasive in Steel programs: the frame
/// rule. All calls to RST functions should be encapsulated inside `rst_frame`. The rule takes 3
/// mandatory arguments:
///  * `outer0` is the resource summming up all the live heap objects when the function `f` is
///    called;
///  * `outer1 x` is the resource summing up all the live heap objects after the function `f`
///    returns with return value `x`;
///  * `f` is the RST function you want to call, with pre and post resources `inner0` and
///    `outer1 x`.
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
        (assert(delta `is_subresource_of` outer0); assert(delta `is_subresource_of` outer1 x);
        focus_rmem h0 delta == focus_rmem h1 delta)
    )
