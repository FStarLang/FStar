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

let length_view_as_seq #a h b = ()

let index (#a:Type) (b:A.array a) (i:UInt32.t) = A.index b i

let upd (#a:Type) (b:A.array a) (i:UInt32.t) (v:a) =
  reveal_rst_inv();
  reveal_modifies();
  (**) let h0 = HST.get () in
  A.upd b i v;
  (**) let h1 = HST.get () in
  assert(modifies (array_resource b) (array_resource b) h0 h1);
  assert(A.loc_includes (A.loc_not_unused_in h0) (as_loc (fp (array_resource b))));
  A.loc_includes_adresses_loc_array #a b true; // TODO: find out why this pattern is not triggered
  A.address_liveness_insensitive_addresses (A.frameOf b) (Set.singleton (A.as_addr b));
  assert(A.modifies (A.address_liveness_insensitive_locs) h0 h1);
  A.modifies_address_liveness_insensitive_unused_in h0 h1;
  assert(A.loc_includes (A.loc_not_unused_in h1) (as_loc (fp (array_resource b))))

let alloc (#a:Type) (init:a) (len:UInt32.t) =
  reveal_rst_inv();
  reveal_modifies();
  let b = A.alloc init len in
  (**) let h1 = HST.get () in
  assert(forall (i:nat{i < A.vlength #a b}). A.get_perm #a h1 b i = FStar.Real.one); // Find out how to trigger that
  A.loc_includes_adresses_loc_array #a b true;
  b

let free (#a:Type) (b:A.array a) =
   reveal_empty_resource();
   reveal_rst_inv();
   reveal_modifies();
   A.free b

let share #a b =
  reveal_rst_inv();
  reveal_modifies();
  reveal_star();
  let b' = A.share b in
  b'

let merge #a b b' =
  reveal_rst_inv();
  reveal_modifies();
  reveal_star();
  A.merge #a b b'
