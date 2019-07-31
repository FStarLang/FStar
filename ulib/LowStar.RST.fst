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

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

open LowStar.Array
open LowStar.Resource

(* Abstract modifies clause for the resource-indexed state effect *)

let frame_usedness_preservation (l1 l2:loc) (h0 h1:HS.mem)
  = forall (frame: loc) .
      (loc_disjoint frame l1 /\
      loc_includes (loc_used_in h0) frame)
      ==>
      (loc_disjoint frame l2 /\
      loc_includes (loc_used_in h1) frame)

let frame_usedness_preservation_intro (l1 l2: loc) (h0 h1:HS.mem)
  (lemma: (frame: loc) -> Lemma
    (requires ((loc_disjoint frame l1) /\ loc_includes (loc_used_in h0) frame))
    (ensures (loc_disjoint frame l2 /\ loc_includes (loc_used_in h1) frame))
  ) : Lemma (frame_usedness_preservation l1 l2 h0 h1)
  =
  let aux (frame: loc) : Lemma ( (loc_disjoint frame l1 /\
      loc_includes (loc_used_in h0) frame)
      ==>
      (loc_disjoint frame l2 /\
      loc_includes (loc_used_in h1) frame))
    =
    let aux (_: squash (loc_disjoint frame l1 /\  loc_includes (loc_used_in h0) frame)) :
      Lemma (loc_disjoint frame l2 /\ loc_includes (loc_used_in h1) frame)
      = lemma frame
    in Classical.impl_intro aux
  in
  Classical.forall_intro aux

let frame_usedness_preservation_elim (l1 l2: loc) (h0 h1:HS.mem) (frame: loc) : Lemma
  (requires (frame_usedness_preservation l1 l2 h0 h1 /\ (loc_disjoint frame l1) /\ loc_includes (loc_used_in h0) frame))
  (ensures (loc_disjoint frame l2 /\ loc_includes (loc_used_in h1) frame))
  = ()

abstract
let modifies (res0 res1:resource) (h0 h1:HS.mem) =
    modifies (as_loc (fp res0)) h0 h1 /\
    frame_usedness_preservation (as_loc (fp res0)) (as_loc (fp res1)) h0 h1

let modifies_refl (res:resource) (h:HS.mem)
  : Lemma (modifies res res h h)
           [SMTPat (modifies res res h h)] =
  ()

let modifies_trans (res0 res1 res2:resource) (h0 h1 h2:HS.mem)
  : Lemma (requires
             modifies res0 res1 h0 h1 /\
             modifies res1 res2 h1 h2)
           (ensures
             modifies res0 res2 h0 h2)
           [SMTPat (modifies res0 res2 h0 h2);
            SMTPat (modifies res0 res1 h0 h1)] =
  modifies_loc_disjoint (as_loc (fp res0)) (as_loc (fp res1)) h0 h1 h2

let reveal_modifies ()
  : Lemma (forall res0 res1 h0 h1.{:pattern modifies res0 res1 h0 h1}
             modifies res0 res1 h0 h1 <==>
             LowStar.Array.modifies (as_loc (fp res0)) h0 h1 /\
             frame_usedness_preservation (as_loc (fp res0)) (as_loc (fp res1)) h0 h1
          )
  = ()

(* State effect indexed by resources *)

let is_subresource_of (r0 r: resource) = exists (r1: resource). r `can_be_split_into` (r0, r1)

let is_subresource_of_elim
  (r0 r: resource)
  (goal: Type)
  (lemma: (r1: resource) -> Lemma (requires (r `can_be_split_into` (r0 , r1))) (ensures goal))
: Lemma
  (requires (r0 `is_subresource_of` r))
  (ensures goal)
  =
  let pf: squash (exists (r1: resource). r `can_be_split_into` (r0, r1)) = () in
  Classical.exists_elim goal #resource #(fun r1 -> r `can_be_split_into` (r0 , r1)) pf (fun r1 ->
    lemma r1
  )

let is_subresource_of_intro (r0 r r1: resource) : Lemma
  (requires (r `can_be_split_into` (r0, r1)))
  (ensures (r0 `is_subresource_of` r))
  = ()

let is_subresource_of_trans (r1 r2 r3: resource) : Lemma
  (requires (r1 `is_subresource_of` r2 /\ r2 `is_subresource_of` r3))
  (ensures (r1 `is_subresource_of` r3))
  =
  is_subresource_of_elim r1 r2 (r1 `is_subresource_of` r3) (fun delta12 ->
    is_subresource_of_elim r2 r3 (r1 `is_subresource_of` r3) (fun delta23 ->
      assert(r3 `can_be_split_into` (r2, delta23));
      assert(r2 `can_be_split_into` (r1, delta12));
      reveal_can_be_split_into ();
      reveal_star ();
      let delta13 = delta12 <*> delta23 in
      loc_union_assoc (as_loc (fp delta23)) (as_loc (fp delta12)) (as_loc (fp r1));
      assert(r3 `can_be_split_into` (r1, delta13));
      is_subresource_of_intro r1 r3 delta13
    )
  )

open FStar.FunctionalExtensionality

let selector r = restricted_g_t (r0:resource{r0 `is_subresource_of` r}) (fun r0 -> r0.t)

let mk_selector
  (r: resource)
  (h: imem (inv r)) :
  (s:selector r{forall (r0:resource{r0 `is_subresource_of` r}). s r0 == r0.view.sel h})
=
  on_dom_g (r0:resource{r0 `is_subresource_of` r}) (fun (r0:resource{r0 `is_subresource_of` r}) -> r0.view.sel h)

let focus_selector (r: resource) (s: selector r) (r0: resource{r0 `is_subresource_of` r}) : selector r0 =
   on_dom_g (r0':resource{r0' `is_subresource_of` r0}) (fun (r0':resource{r0' `is_subresource_of` r0}) ->
     is_subresource_of_trans r0' r0 r;
     s r0'
   )

let hsprop (r: resource) : Type = selector r -> Type0

let extend_hsprop (r0: resource) (p: hsprop r0) (r: resource{r0 `is_subresource_of` r}) : hsprop r =
  fun s -> p (focus_selector r s r0)

#push-options "--z3rlimit 30"

let hsrefine (r:resource) (p:hsprop r) : resource =
  let new_inv (h: HS.mem) = r.view.inv h /\ p (mk_selector r h) in
  let new_view = { r.view with inv = new_inv } in
  reveal_view ();
  let open LowStar.Array in
  assert(sel_reads_fp new_view.fp new_view.inv new_view.sel);
  let aux (h0 h1: HS.mem) (loc: loc) : Lemma (
    new_view.inv h0 /\
    loc_disjoint (as_loc new_view.fp) loc /\ modifies loc h0 h1 ==>
    new_view.inv h1
  ) =
    let aux (_ : squash ( new_view.inv h0 /\ loc_disjoint (as_loc new_view.fp) loc /\ modifies loc h0 h1)) : Lemma (new_view.inv h1) =
      assert(r.view.inv h1);
      assert(p (mk_selector r h0));
      let sel0 = mk_selector r h0 in
      let sel1 = mk_selector r h1 in
      let aux (r0: resource{r0 `is_subresource_of` r}) : Lemma (sel0 r0 == sel1 r0) =
        reveal_can_be_split_into ();
        assert(r0.view.sel h0 == r0.view.sel h1)
      in
      Classical.forall_intro aux;
      let open FStar.FunctionalExtensionality in
      let a = r0:resource{r0 `is_subresource_of` r} in
      let b = fun r0 -> r0.t in
      extensionality_g a b sel0 sel1
    in
    Classical.impl_intro aux
  in
  Classical.forall_intro_3 aux;
  assert(inv_reads_fp new_view.fp new_view.inv);
  { r with view = new_view }

#pop-options

let refine_preserves_splitting (res0 delta res1: resource) (p: hsprop res0) : Lemma
  (res0 `can_be_split_into` (res1,delta) <==> hsrefine res0 p `can_be_split_into` (res1,delta))
  =
  reveal_can_be_split_into ();
  let aux (_ : squash (res0 `can_be_split_into` (res1,delta))) : Lemma (hsrefine res0 p `can_be_split_into` (res1,delta)) =
    admit()
  in
  let aux' (_ : squash (hsrefine res0 p `can_be_split_into` (res1,delta))) : Lemma (res0 `can_be_split_into` (res1,delta)) =
    admit()
  in
  Classical.impl_intro aux;
  Classical.impl_intro aux'

let refine_selector (r: resource) (s:selector r) (p: hsprop r{p s}) : selector (hsrefine r p) =
  on_dom_g (r0:resource{r0 `is_subresource_of` (hsrefine r p)}) (fun (r0:resource{r0 `is_subresource_of` (hsrefine r p)}) ->
     is_subresource_of_elim r0 (hsrefine r p) (r0 `is_subresource_of` r) (fun delta ->
       refine_preserves_splitting r delta r0 p
     );
     s r0
   )

let r_pre (res:resource) =  hsprop res
let r_post
  (res0: resource)
  (pre: r_pre res0)
  (a: Type)
  (res1: a -> resource) =
  selector (hsrefine res0 pre) -> x:a -> hsprop (res1 x)

abstract
let rst_inv (res:resource) (h:HS.mem) : GTot prop =
  loc_includes (loc_used_in  h) (as_loc (fp res)) /\ True

let reveal_rst_inv ()
  : Lemma (forall res h .
             rst_inv res h
             <==>
             loc_includes (loc_used_in  h) (as_loc (fp res)))
  = ()

let rst_inv_star (res0 res1: resource) (h: HS.mem) : Lemma
  (rst_inv (res0 <*> res1) h <==> rst_inv (res1 <*> res0) h)
  [SMTPat (rst_inv (res0 <*> res1) h)]
  = reveal_star ()

// Monotonic WPs for RSTATE
let rstate_wp (a:Type) (res0:resource) (res1:a -> resource) =
  wp:((x:a -> imem (inv (res1 x)) -> Type0) -> imem (inv res0) -> Type0){
      forall (p q:(x:a -> imem (inv (res1 x)) -> Type0)) h0 .
        (forall x h1 . p x h1 ==> q x h1) ==> wp p h0 ==> wp q h0
    }

effect RSTATE (a:Type)
              (res0:resource)                                   // Pre-resource (expected from the caller)
              (res1:a -> resource)                              // Post-resource (returned back to the caller)
              (wp:rstate_wp a res0 res1) =
       STATE a
           (fun (p:a -> HS.mem -> Type)
              (h0:HS.mem) ->
                inv res0 h0 /\                                  // Require the pre-resource invariant
                rst_inv res0 h0 /\                              // Require the additional footprints invariant
                wp (fun x h1 ->
                     inv (res1 x) h1 /\                         // Ensure the post-resource invariant
                     rst_inv (res1 x) h1 /\                     // Ensure the additional footprints invariant
                     modifies res0 (res1 x) h0 h1 ==>           // Ensure that at most resources' footprints are modified
                     p x h1) h0)                                // Prove the continuation under this hypothesis

(* Pre- and postcondition style effect RST *)

effect RST0
  (a:Type)
  (res0:resource)
  (res1:a -> selector res0 -> resource)
= ST a
  (fun h0 -> res0.view.inv h0)
  (fun h0 x h1 -> (res1 x (mk_selector res0 h0)).view.inv h1)

effect RST
  (a: Type)
  (res0: resource)
  (res1: a -> resource)
  (pre: r_pre res0)
  (post: r_post res0 pre a res1)
= RST0
  a
  (hsrefine res0 pre)
  (fun x old -> hsrefine (res1 x) (post old x))

(* Bind operation for RSTATE *)

let bind
  (#a #b:Type)
  (#res0:resource)
  (#res1:a -> resource)
  (#res2:b -> resource)
  (#wp0:rstate_wp a res0 res1)
  (#wp1:(x:a -> rstate_wp b (res1 x) res2))
  (f:unit -> RSTATE a res0 res1 wp0)
  (g:(x:a -> RSTATE b (res1 x) res2 (wp1 x)))
: RSTATE b res0 res2 (fun p h0 -> wp0 (fun x h1 -> wp1 x p h1) h0) =
  g (f ())

open LowStar.RST.Tactics

let frame_wp
  (#outer0:resource)
  (#inner0:resource)
  (#a:Type)
  (#outer1:a -> resource)
  (#inner1:a -> resource)
  (delta:resource{frame_delta outer0 inner0 outer1 inner1 delta})
  (wp:rstate_wp a inner0 inner1)
: rstate_wp a outer0 outer1 =
  fun p h0 ->
    wp (fun x (h1:imem (inv (inner1 x))) ->
      inv (outer1 x) h1 /\
      sel (view_of delta) h0 == sel (view_of delta) h1
      ==>
      p x h1)
    h0

inline_for_extraction noextract let frame
  (outer0:resource)
  (#inner0:resource)
  (#a:Type)
  (outer1:a -> resource)
  (#inner1:a -> resource)
  (#[resolve_delta ()]
    delta:resource{frame_delta outer0 inner0 outer1 inner1 delta})
  (#wp:rstate_wp a inner0 inner1)
  ($f:unit -> RSTATE a inner0 inner1 wp)
: RSTATE a outer0 outer1 (frame_wp delta wp) =
  reveal_view ();
  reveal_can_be_split_into ();
  f ()

(* Generic framing operation for RST (through resource inclusion) *)

unfold let frame_pre
  (#outer0:resource)
  (#inner0:resource)
  (delta:resource{frame_delta_pre outer0 inner0 delta})
  (pre:r_pre inner0)
  (old: selector outer0) =
  pre (focus_selector outer0 old inner0)

unfold
let frame_post
  (#outer0:resource)
  (#inner0:resource)
  (#a:Type)
  (#outer1:a -> resource)
  (#inner1:a -> resource)
  (delta:resource{frame_delta outer0 inner0 outer1 inner1 delta})
  (pre:r_pre inner0)
  (post:r_post inner0 pre a inner1)
  (old:selector outer0)
  (x:a)
  (modern:selector (outer1 x))
=
  reveal_can_be_split_into ();
  pre (focus_selector outer0 old inner0) /\
  post
    (refine_selector inner0 (focus_selector outer0 old inner0) pre)
    x
    (focus_selector (outer1 x) modern (inner1 x)) /\
  old delta == modern delta


#set-options "--no_tactics"

let get (r: resource) : RST0
  (selector r)
  (r)
  (fun _ _ -> r)
  =
  let h = HST.get () in
  mk_selector r h


// [DA: should be definable directly using RSTATE frame, but get
//      an error about unexpected unification variable remaining]
inline_for_extraction noextract let rst_frame
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
   (#pre:r_pre inner0)
   (#post:r_post inner0 pre a inner1)
   ($f:unit -> RST a inner0 inner1 pre post)
: RST a outer0 outer1
  (FStar.Tactics.by_tactic_seman resolve_frame_delta (frame_delta outer0 inner0 outer1 inner1 delta);
    frame_pre delta pre
  )
  (refine_preserves_splitting outer0 delta inner0 (frame_pre delta pre);
    frame_post delta pre post)
=
  reveal_view ();
  reveal_can_be_split_into ();
  FStar.Tactics.by_tactic_seman resolve_frame_delta (frame_delta outer0 inner0 outer1 inner1 delta);
  admit();
  f ()
