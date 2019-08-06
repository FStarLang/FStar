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
module LowStar.Resource

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

open LowStar.Array

#set-options "--z3rlimit 10"

(* Views and resources *)

let sel_reads_fp #b fp inv sel =
  forall (h0 h1:imem inv) loc. {:pattern (modifies loc h0 h1); (sel h1)}
    loc_disjoint (as_loc fp) loc /\
    modifies loc h0 h1 ==>
    sel h0 == sel h1

let inv_reads_fp fp inv =
  forall h0 h1 loc.{:pattern (modifies loc h0 h1); (inv h1)}
    inv h0 /\
    loc_disjoint (as_loc fp) loc /\
    modifies loc h0 h1 ==>
    inv h1

let reveal_view () = ()

let ( <*> ) (res1 res2:resource) : res:resource =
  let inv (h: HS.mem) : prop = inv res1 h /\ inv res2 h /\ loc_disjoint (as_loc (fp res1)) (as_loc (fp res2)) in
  let fp = Ghost.hide (loc_union (as_loc (fp res1)) (as_loc (fp res2))) in
  let sel (h: HS.mem) : GTot (res1.t & res2.t) = (sel res1.view h,sel res2.view h) in
  let t = res1.t & res2.t in
  let view = {
      fp = fp;
      inv = inv;
      sel = sel
    } in
  let out = {
    t = t;
    view = view
  } in
  out

let reveal_star_inv res1 res2 h = ()

let reveal_star_sel res1 res2 h = ()

let reveal_star () = ()

let empty_resource : resource =
  reveal_view ();
  let fp = Ghost.hide loc_none in
  let inv (h : HS.mem) : prop = True in
  let sel h = () in
  let t = unit in
  let (view:view t) = {
      fp = fp;
      inv = inv;
      sel = sel
    }
  in
  {
    t = t;
    view = view
  }

let reveal_empty_resource () = ()


let can_be_split_into (outer:resource) ((inner,delta):resource & resource) =
    as_loc (fp outer) == loc_union (as_loc (fp delta)) (as_loc (fp inner)) /\
    (forall h . inv outer h <==> inv inner h /\ inv delta h /\ loc_disjoint (as_loc (fp delta)) (as_loc (fp inner)))

let reveal_can_be_split_into () = ()

let star_can_be_split_into_parts res1 res2 = ()

let star_can_be_split_into_parts' res1 res2 = ()

let can_be_split_into_empty_left res = ()

let can_be_split_into_empty_reverse_left res1 res2 = ()

let can_be_split_into_empty_right res = ()

let can_be_split_into_empty_reverse_right res1 res2 = ()

let reveal_can_be_split_into_inner_inv outer inner delta h = ()

let reveal_can_be_split_into_delta_inv outer inner delta h = ()

let equal (res1 res2:resource) =
    res1 `can_be_split_into` (res2,empty_resource)

let equal_refl res = ()

let equal_symm res1 res2 = ()

let equal_trans res1 res2 res3 = ()

let equal_comm_monoid_left_unit res = ()

let equal_comm_monoid_right_unit res = ()

let equal_comm_monoid_commutativity res1 res2 = ()

let equal_comm_monoid_associativity res1 res2 res3 =
  loc_union_assoc (as_loc (fp res1)) (as_loc (fp res2)) (as_loc (fp res3));
  ()

let equal_comm_monoid_cong res1 res2 res3 res4 = ()

(* `can_be_split_into` follows from equality to `<*>` (called in frame resolution) *)

let can_be_split_into_star res1 res2 res3 = ()
