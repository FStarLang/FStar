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

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

open LowStar.Array
open Steel.Resource


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
    modifies (as_loc (fp res0) h0) h0 h1 /\
    frame_usedness_preservation (as_loc (fp res0) h0) (as_loc (fp res1) h1) h0 h1

let reveal_modifies () = ()

let modifies_refl res h = ()

let modifies_trans res0 res1 res2 h0 h1 h2 =
  modifies_loc_disjoint (as_loc (fp res0) h0) (as_loc (fp res1) h1) h0 h1 h2

let is_subresource_of_elim r0 r goal lemma =
  let pf: squash (exists (r1: resource). r `can_be_split_into` (r0, r1)) = () in
  Classical.exists_elim goal #resource #(fun r1 -> r `can_be_split_into` (r0 , r1)) pf (fun r1 ->
    lemma r1
  )

let is_subresource_of_intro1 r0 r r1 = ()

let is_subresource_of_intro2 r0 r r1 = reveal_can_be_split_into ()

let is_subresource_of_trans r1 r2 r3 =
  is_subresource_of_elim r1 r2 (r1 `is_subresource_of` r3) (fun delta12 ->
    is_subresource_of_elim r2 r3 (r1 `is_subresource_of` r3) (fun delta23 ->
      can_be_split_into_trans r3 r2 r1 delta23 delta12
    )
  )

#push-options "--no_tactics"

let is_subresource_of_refl r =
  assert(r `can_be_split_into` (r, empty_resource))


open FStar.FunctionalExtensionality

#pop-options

let mk_rmem r h =
   Fext.on_dom_g
     (r0:resource{r0 `is_subresource_of` r})
     (fun (r0:resource{r0 `is_subresource_of` r}) -> sel r0.view h)

let focus_rmem' (#r: resource) (s: rmem r) (r0: resource{r0 `is_subresource_of` r})
  : Tot (s':rmem r0{forall (r0':resource{r0' `is_subresource_of` r0}).
    (is_subresource_of_trans r0' r0 r; s' r0' == s r0')
  }) =
  let r' =
    Fext.on_dom_g
      (r0':resource{r0' `is_subresource_of` r0})
      (fun (r0':resource{r0' `is_subresource_of` r0}) ->
        is_subresource_of_trans r0' r0 r; s r0'
      )
  in r'


let focus_rmem #r s #delta r0 =
  focus_rmem' #r s r0

let focus_rmem_equality outer inner arg #delta1  h =
  let focused = focus_rmem h #delta1 inner in
  extensionality_g
    (r0:resource{r0 `is_subresource_of` inner})
    (fun r0 -> r0.t)
    focused
    (fun r0 -> is_subresource_of_trans r0 inner outer; h r0)

let extend_rprop #r0 p #delta r =
    fun s -> p (focus_rmem #r s #delta r0)

#push-options "--z3rlimit 30"

let hsrefine r p =
  let new_inv (h: HS.mem) : prop = r.view.inv h /\ p (mk_rmem r h) in
  let new_view = { r.view with inv = new_inv } in
  reveal_view ();
  let open LowStar.Array in
  assert(sel_reads_fp new_view.fp new_view.inv new_view.sel);
  let aux (h0 h1: HS.mem) (loc: loc) : Lemma (
    new_view.inv h0 /\
    loc_disjoint (as_loc new_view.fp h0) loc /\ modifies loc h0 h1 ==>
    new_view.inv h1
  ) =
    let aux (_ : squash (
      new_view.inv h0 /\ loc_disjoint (as_loc new_view.fp h0) loc /\ modifies loc h0 h1
    )) : Lemma (new_view.inv h1) =
      assert(r.view.inv h1);
      assert(p (mk_rmem r h0));
      let sel0 = mk_rmem r h0 in
      let sel1 = mk_rmem r h1 in
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
  loc_includes (loc_used_in h) (as_loc (fp res) h) /\ True

let reveal_rst_inv () = ()

let rst_inv_star res0 res1 h = reveal_star ()



open Steel.Tactics

(* Generic framing operation for RST (through resource inclusion) *)

let get r =
  let h = HST.get () in
  mk_rmem r h

val focus_mk_rmem_equality (outer inner: resource) (#delta: resource) (h: HS.mem)
  : Lemma
    (requires (inv outer h /\ outer `can_be_split_into` (inner,delta)))
    (ensures (is_subresource_of_elim inner outer (inv inner h) (fun _ -> ());
      focus_rmem (mk_rmem outer h) #delta inner == mk_rmem inner h))

let focus_mk_rmem_equality outer inner #delta h =
  let souter = mk_rmem outer h in
  let focused = focus_rmem souter #delta inner in
  let original = mk_rmem inner h in
  extensionality_g
    (r0:resource{r0 `is_subresource_of` inner})
    (fun r0 -> r0.t)
    focused
    original;
  let aux
    (delta2: resource)
    (r0:resource{inner `can_be_split_into` (r0, delta2)}) : Lemma (focused r0 == original r0) =
    focus_rmem_equality outer inner r0 #delta souter;
    is_subresource_of_trans r0 inner outer
  in
    Classical.forall_intro_2 aux

#push-options "--no_tactics --z3rlimit 200 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract let rst_frame
  outer0 #inner0 #a outer1 #inner1 #delta #pre #pos f
  =
  (**) reveal_view ();
  (**) reveal_can_be_split_into ();
  (**) reveal_rst_inv ();
  (**) FStar.Tactics.by_tactic_seman resolve_frame_delta
  (**)   (frame_delta outer0 inner0 outer1 inner1 delta);
  (**) let h0 = HST.get () in
  (**) let rh0 = mk_rmem outer0 h0 in
  (**) focus_mk_rmem_equality outer0 inner0 #delta h0;
  (**) focus_mk_rmem_equality outer0 delta #inner0 h0;
  let x = f () in
  (**) let h1 = HST.get () in
  (**) let rh1 = mk_rmem (outer1 x) h1 in
  (**) focus_mk_rmem_equality (outer1 x) (inner1 x) #delta h1;
  (**) focus_mk_rmem_equality (outer1 x) delta #(inner1 x) h1;
  (**) let old_delta = focus_rmem (mk_rmem outer0 h0) #inner0 delta in
  (**) let cur_delta = focus_rmem (mk_rmem (outer1 x) h1) #(inner1 x) delta in
  (**) extensionality_g
  (**)   (r0:resource{r0 `is_subresource_of` delta})
  (**)   (fun r0 -> r0.t)
  (**)   old_delta
  (**)   cur_delta;
  x

#pop-options
