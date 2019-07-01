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
module LowStar.RST.Array

let index (#a:Type) (b:A.array a) (i:UInt32.t) = reveal_array(); A.index b i

let upd (#a:Type) (b:A.array a) (i:UInt32.t) (v:a) =
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  (**) let h0 = HST.get () in
  A.upd b i v;
  (**) let h1 = HST.get () in
  (**) assert(modifies (array_resource b) (array_resource b) h0 h1);
  (**) assert(A.loc_includes (A.loc_not_unused_in h0) (as_loc (fp (array_resource b))));
  (**) A.loc_includes_adresses_loc_array #a b true; // TODO: find out why this pattern is not triggered
  (**) A.address_liveness_insensitive_addresses (A.frameOf b) (Set.singleton (A.as_addr b));
  (**) assert(A.modifies (A.address_liveness_insensitive_locs) h0 h1);
  (**) A.modifies_address_liveness_insensitive_unused_in h0 h1;
  (**) assert(A.loc_includes (A.loc_not_unused_in h1) (as_loc (fp (array_resource b))));
  (**) same_perm_seq_always_constant h0 h1 b

let alloc (#a:Type) (init:a) (len:UInt32.t) =
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  let b = A.alloc init len in
  (**) let h1 = HST.get () in
  (**) assert(forall (i:nat{i < A.vlength #a b}). A.get_perm #a h1 b i = FStar.Real.one); // Find out how to trigger that
  (**) A.loc_includes_adresses_loc_array #a b true;
  b

let free (#a:Type) (b:A.array a) =
  (**) reveal_array();
  (**) reveal_empty_resource();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  A.free b

let share #a b =
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  (**) reveal_star();
  let b' = A.share b in
  b'

let merge #a b b' =
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  (**) reveal_star();
  A.merge #a b b'

let split #a b idx =
  (**) reveal_array ();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  (**) let h0 = HST.get () in
  let (b1, b2) = A.split #a b idx in
  (**) let h1 = HST.get () in
  (**) reveal_star_inv (array_resource b1) (array_resource b2) h1;
  (**) let aux1 (i:nat{i < A.vlength b1}) (j:nat{j < A.vlength b1}) : Lemma (A.get_perm h1 b1 i == A.get_perm h1 b1 j) =
  (**)   assert(A.get_perm h1 b1 i = A.get_perm h0 b i);
  (**)   assert(A.get_perm h1 b1 j = A.get_perm h0 b j)
  (**) in
  (**) Classical.forall_intro_2 aux1;
  (**) let aux2 (i:nat{i < A.vlength b2}) (j:nat{j < A.vlength b2}) : Lemma (A.get_perm h1 b2 i == A.get_perm h1 b2 j) =
  (**)   assert(A.get_perm h1 b2 i = A.get_perm h0 b (i + A.vlength b1));
  (**)   assert(A.get_perm h1 b2 j = A.get_perm h0 b (j + A.vlength b1))
  (**) in
  (**) Classical.forall_intro_2 aux2;
  (**) assert(forall(i:nat{i < A.vlength b2}). (A.get_perm h1 b2 i == A.get_perm h0 b (i + A.vlength b1)));
  (b1, b2)
