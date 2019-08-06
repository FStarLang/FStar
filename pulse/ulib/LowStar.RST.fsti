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
module LowStar.RST

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module A = LowStar.Array
module R = LowStar.Resource

/// The `RST` effect is the top concept of the Steel framework. It offers a way of specifying function in terms of resources, abstracting
/// away the `modifies` theory of `LowStar.Array`.

(**** Abstract modifies clause for the resource-indexed state effect *)

/// Because this new state effect will only talk about heap modifications structured in terms of resources, we can refine the notion of
/// `modifies`. More precisely, if `l1` is modified into `l2` when going from heap `h0` to heap `h1`, then every other used region of
/// the heap stays disjoint from the modifies region and stays used. It morally means that any growth in the modified region induced by
/// a function does not touch existing used locations.
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
    (requires (frame_usedness_preservation l1 l2 h0 h1 /\ (A.loc_disjoint frame l1) /\ A.loc_includes (A.loc_used_in h0) frame))
    (ensures (A.loc_disjoint frame l2 /\ A.loc_includes (A.loc_used_in h1) frame))

/// We can now define our new `modifies` in terms of resources.
val modifies (res0 res1:R.resource) (h0 h1:HS.mem) : prop

val reveal_modifies (_ : unit)
  : Lemma (forall res0 res1 h0 h1.{:pattern modifies res0 res1 h0 h1}
    modifies res0 res1 h0 h1 <==>
      A.modifies (R.as_loc (R.fp res0)) h0 h1 /\
      frame_usedness_preservation (R.as_loc (R.fp res0)) (R.as_loc (R.fp res1)) h0 h1
   )

val modifies_refl (res:R.resource) (h:HS.mem)
  : Lemma (modifies res res h h)
  [SMTPat (modifies res res h h)]

val modifies_trans (res0 res1 res2:R.resource) (h0 h1 h2:HS.mem)
  : Lemma
    (requires (modifies res0 res1 h0 h1 /\ modifies res1 res2 h1 h2))
    (ensures (modifies res0 res2 h0 h2))
  [SMTPat (modifies res0 res2 h0 h2); SMTPat (modifies res0 res1 h0 h1)]

(**** Subresources *)

/// `LowStar.Resource` defines `can_be_split_into`, but we need here an existential predicate to not carry around all the splitting deltas.
let is_subresource_of (r0 r: R.resource) = exists (r1: R.resource). r `R.can_be_split_into` (r0, r1)

val is_subresource_of_elim
  (r0 r: R.resource)
  (goal: Type)
  (lemma: (r1: R.resource) -> Lemma (requires (r `R.can_be_split_into` (r0 , r1))) (ensures goal))
  : Lemma
    (requires (r0 `is_subresource_of` r))
    (ensures goal)

val is_subresource_of_intro (r0 r r1: R.resource)
  : Lemma
    (requires (r `R.can_be_split_into` (r0, r1)))
    (ensures (r0 `is_subresource_of` r))

val is_subresource_of_trans (r1 r2 r3: R.resource)
  : Lemma
    (requires (r1 `is_subresource_of` r2 /\ r2 `is_subresource_of` r3))
    (ensures (r1 `is_subresource_of` r3))
  [SMTPat (r1 `is_subresource_of` r2); SMTPat (r2 `is_subresource_of` r3); SMTPat (r1 `is_subresource_of` r3)]

val is_subresource_of_refl (r: R.resource) : Lemma(r `is_subresource_of` r) [SMTPat (r `is_subresource_of` r)]

(**** Selectors *)

/// The spirit of `LowStar.Resource` is to limit our reasonning to a fragment of the heap. For the `RST` effect, we push this idea
/// further and we will no longer allow to speak about the entirety of the heap inside pre and postconditions. Rather, we want to be only
/// able to talk about the resources at hand.

module Fext =  FStar.FunctionalExtensionality

/// We extend on the `LowStar.Resource.sel_t` selector type by allowing our new selectors to also talk about the subresources contained
/// inside the enclosing resource. Selectors are morally `(r0:R.resource{r0 is_subresource_of r}) -> r0.R.t`, but we need to define
/// them with functional extensionality.
let selector (r: R.resource) : Type = Fext.restricted_g_t (r0:R.resource{r0 `is_subresource_of` r}) (fun r0 -> r0.R.t)

/// The main way to make a selector is to derive one from a particular state of the heap. `mk_selector r h` effectively restricts your
/// access to the heap to accesses that are valid and withing the resource you consider.
val mk_selector
  (r: R.resource)
  (h: R.imem (R.inv r)) :
  Tot (s:selector r{forall (r0:R.resource{r0 `is_subresource_of` r}). s r0 == R.sel r0.R.view h})

/// The only other transformation allowed on selectors is focusing on a subresource.
val focus_selector (#r: R.resource) (s: selector r) (r0: R.resource{r0 `is_subresource_of` r})
  : Tot (selector r0)

val focus_selector_equality (outer inner: R.resource) (h: HS.mem)
  : Lemma
    (requires (R.inv outer h /\ inner `is_subresource_of` outer))
    (ensures (focus_selector (mk_selector outer h) inner == mk_selector inner h))
    [SMTPat (focus_selector (mk_selector outer h) inner)]

/// In the ST state, pre and postconditions depended on the entire heap. Here, theses conditions depend only on a `selector` for the
/// resource at hand (derived from a heap state).
let sprop r = selector r -> Type0

/// `extend_sprop` is the dual of `focus_selector`.
val extend_sprop (#r0: R.resource) (p: sprop r0) (r: R.resource{r0 `is_subresource_of` r}) : Tot (sprop r)

/// Thanks to selectors, we can define abstract resource refinements that strenghten the invariant of a resource.
val hsrefine (r:R.resource) (p:sprop r) : R.resource

val reveal_hsrefine (r:R.resource) (p: sprop r)
  : Lemma (
    let r' = hsrefine r p in
    forall (h: R.imem (R.inv r)).
      r'.R.t == r.R.t /\
      R.sel r'.R.view h == R.sel r.R.view h /\
      R.fp r' == R.fp r /\
      (R.inv r' h <==> R.inv r h /\ p (mk_selector r h))
  )

(**** The RST effect *)

/// On top of the invariants of the resource at hand, we add another global invariant governing how resources are used :
/// The footprint of resources used in Steel functions have to be used.
val rst_inv (res:R.resource) (h:HS.mem) : GTot prop

val reveal_rst_inv (_ : unit)
  : Lemma (forall res h .
    rst_inv res h <==>
      A.loc_includes (A.loc_used_in h) (R.as_loc (R.fp res))
  )

val rst_inv_star (res0 res1: R.resource) (h: HS.mem)
  : Lemma (rst_inv R.(res0 <*> res1) h <==> rst_inv R.(res1 <*> res0) h)
  [SMTPat (rst_inv R.(res0 <*> res1) h)]

let r_pre (res:R.resource) =  sprop res
let r_post
  (res0: R.resource)
  (a: Type)
  (res1: a -> R.resource) =
  selector res0 -> x:a -> sprop (res1 x)


/// Finally, the RST effect. Eventually with the layered effects, its definition will be hidden here. It has five indexes:
///  * the return type;
///  * the initial resource, which is the composite heap object formed by all the arguments to the function;
///  * the final resource, which is the composite heap object alive at then end of the function (and depends on the return value);
///  * the precondition, which is an `sprop` of the initial resource and should be used to indicate the functional specification of the
///    function, since all of the memory shape specification has been dealt with in the two previous indexes;
///  * the postcondition, function of the initial and final resources selectors and the return value.
/// The pre/postcondition of the `ST` effect have been split in two. First, you specify what happens to the memory: what heap objects are
/// live at the beginning, how the function transforms this memory shape. Then, you can add traditionnal functional specification but,
/// thanks to selectors, these functional specification can only depend on the views of the resources you're handling.
effect RST
  (a: Type)
  (res0: R.resource)
  (res1: a -> R.resource)
  (pre: sprop res0)
  (post: selector res0 -> (x:a) -> sprop (res1 x))
= ST.ST
  a
  (fun h0 -> R.inv res0 h0 /\ rst_inv res0 h0 /\ pre (mk_selector res0 h0))
  (fun h0 x h1 ->
    R.inv res0 h0 /\ rst_inv res0 h0 /\ pre (mk_selector res0 h0) /\
    R.inv (res1 x) h1 /\
    rst_inv (res1 x) h1 /\
    modifies res0 (res1 x) h0 h1 /\
    post (mk_selector res0 h0) x (mk_selector (res1 x) h1)
  )

/// Similar to `FStar.Hyperstack.ST.get`, this helper gives you a selector based on the current state of the heap
val get (r: R.resource) : RST
  (selector r)
  (r)
  (fun _ -> r)
  (fun _ -> True)
  (fun old returned cur -> returned == old /\ old == cur)

#set-options "--no_tactics"

open LowStar.RST.Tactics

inline_for_extraction noextract val rst_frame
  (outer0:R.resource)
  (#inner0:R.resource)
  (#a:Type)
  (outer1:a -> R.resource)
  (#inner1:a -> R.resource)
  (#[resolve_delta ()]
     delta:R.resource{
       FStar.Tactics.with_tactic
         resolve_frame_delta
         (frame_delta outer0 inner0 outer1 inner1 delta)
     }
   )
  (#pre:sprop inner0)
  (#post:selector inner0 -> (x:a) -> sprop (inner1 x))
   ($f:unit -> RST a inner0 inner1 pre post)
  : RST a outer0 outer1
    (FStar.Tactics.by_tactic_seman resolve_frame_delta (frame_delta outer0 inner0 outer1 inner1 delta);
      fun old ->
        pre (focus_selector old inner0)
    )
    (R.reveal_can_be_split_into ();
      fun old x cur ->
        post
          (focus_selector old inner0)
          x
          (focus_selector cur (inner1 x)) /\
        (assert(delta `is_subresource_of` outer0); assert(delta `is_subresource_of` outer1 x);
        focus_selector old delta == focus_selector cur delta)
    )
