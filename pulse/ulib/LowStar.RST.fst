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


let frame_usedness_preservation_intro l1 l2 h0 h1 lemma =
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

let frame_usedness_preservation_elim l1 l2 h0 h1 frame = ()

let modifies res0 res1 h0 h1 =
    modifies (as_loc (fp res0)) h0 h1 /\
    frame_usedness_preservation (as_loc (fp res0)) (as_loc (fp res1)) h0 h1

let reveal_modifies () = ()

let modifies_refl res h = ()

let modifies_trans res0 res1 res2 h0 h1 h2 =
  modifies_loc_disjoint (as_loc (fp res0)) (as_loc (fp res1)) h0 h1 h2


let is_subresource_of r0 r = exists (r1: R.resource). r `R.can_be_split_into` (r0, r1)


let is_subresource_of_elim r0 r goal lemma =
  let pf: squash (exists (r1: resource). r `can_be_split_into` (r0, r1)) = () in
  Classical.exists_elim goal #resource #(fun r1 -> r `can_be_split_into` (r0 , r1)) pf (fun r1 ->
    lemma r1
  )

let can_be_split_into_intro_star r0 r1 = ()

let is_subresource_of_intro1 r0 r r1 = ()

let is_subresource_of_intro2 r0 r r1 = R.reveal_can_be_split_into ()

let is_subresource_of_trans r1 r2 r3 =
  is_subresource_of_elim r1 r2 (r1 `is_subresource_of` r3) (fun delta12 ->
    is_subresource_of_elim r2 r3 (r1 `is_subresource_of` r3) (fun delta23 ->
      assert(r3 `can_be_split_into` (r2, delta23));
      assert(r2 `can_be_split_into` (r1, delta12));
      reveal_can_be_split_into ();
      reveal_star ();
      let delta13 = delta12 <*> delta23 in
      loc_union_assoc (as_loc (fp delta23)) (as_loc (fp delta12)) (as_loc (fp r1));
      assert(r3 `can_be_split_into` (r1, delta13))
    )
  )

let is_subresource_of_refl r =
  assert(r `can_be_split_into` (r, empty_resource))

open FStar.FunctionalExtensionality

let mk_selector r h =
   Fext.on_dom_g (r0:R.resource{r0 `is_subresource_of` r}) (fun (r0:R.resource{r0 `is_subresource_of` r}) -> R.sel r0.R.view h)

let focus_selector' (#r: R.resource) (s: selector r) (r0: R.resource{r0 `is_subresource_of` r})
  : Tot (s':selector r0{forall (r0':resource{r0' `is_subresource_of` r0}). s' r0' == s r0'}) =
   let r' = Fext.on_dom_g (r0':R.resource{r0' `is_subresource_of` r0}) (fun (r0':R.resource{r0' `is_subresource_of` r0}) ->
    s r0'
  ) in r'


let focus_selector #r s r0 =
  focus_selector' #r s r0


let focus_selector_equality outer inner h =
  let souter = mk_selector outer h in
  let focused = focus_selector souter inner in
  let original = mk_selector inner h in
  extensionality_g
    (r0:resource{r0 `is_subresource_of` inner})
    (fun r0 -> r0.t)
    focused
    original

let extend_sprop (#r0: resource) (p: sprop r0) (r: resource{r0 `is_subresource_of` r}) : Tot (sprop r) =
  fun s -> p (focus_selector #r s r0)

#push-options "--z3rlimit 30"

let hsrefine r p =
  let new_inv (h: HS.mem) : prop = r.view.inv h /\ p (mk_selector r h) in
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
      let a = r0:resource{r0 `is_subresource_of` r} in
      let b = fun r0 -> r0.t in
      extensionality_g a b sel0 sel1
    in
    Classical.impl_intro aux
  in
  Classical.forall_intro_3 aux;
  assert(inv_reads_fp new_view.fp new_view.inv);
  let r' = { r with view = new_view } in
  r'

#pop-options

let rst_inv res h =
  loc_includes (loc_used_in  h) (as_loc (fp res)) /\ True

let reveal_rst_inv () = ()

let rst_inv_star res0 res1 h = reveal_star ()



open LowStar.RST.Tactics

(* Generic framing operation for RST (through resource inclusion) *)

#set-options "--no_tactics"

let get r =
  let h = HST.get () in
  mk_selector r h

#set-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 1"

inline_for_extraction noextract let rst_frame
  outer0 #inner0 #a outer1 #inner1 #delta #pre #pos f
  =
  (**) reveal_view ();
  (**) reveal_can_be_split_into ();
  (**) reveal_rst_inv ();
  (**) FStar.Tactics.by_tactic_seman resolve_frame_delta (frame_delta outer0 inner0 outer1 inner1 delta);
  (**) let h0 = HST.get () in
  (**) focus_selector_equality outer0 inner0 h0;
  (**) focus_selector_equality outer0 delta h0;
  let x = f () in
  (**) let h1 = HST.get () in
  (**) focus_selector_equality (outer1 x) (inner1 x) h1;
  (**) focus_selector_equality (outer1 x) delta h1;
  (**) let old = mk_selector outer0 h0 in
  (**) let cur = mk_selector (outer1 x) h1 in
  (**) let old_delta = focus_selector old delta in
  (**) let cur_delta = focus_selector cur delta in
  (**) extensionality_g
  (**)  (r0:resource{r0 `is_subresource_of` delta})
  (**)  (fun r0 -> r0.t)
  (**)  old_delta
  (**)  cur_delta;
  x
