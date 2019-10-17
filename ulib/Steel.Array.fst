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
module Steel.Array

open Steel.RST

#set-options "--max_fuel 0 --max_ifuel 0"


val index_ (#a:Type) (b:A.array a) (i:UInt32.t)
  : rst_repr a (array_resource b)
    (fun _ -> array_resource b)
    (fun _ -> UInt32.v i < A.vlength b)
    (fun h0 x h1 ->
      UInt32.v i < A.vlength b /\
      Seq.index (as_rseq b h0) (UInt32.v i) == x /\
      h0 == h1
    )

#push-options "--admit_smt_queries false"

module ST = FStar.HyperStack.ST

let index_ (#a:Type) (b:A.array a) (i:UInt32.t) =
  fun _ ->
  reveal_array ();
  let h0 = FStar.HyperStack.ST.get () in  
  let x = A.index b i in
  //AR: this assertion is required, else the proof doesn't go through
  //    I suspect some patterns not set up properly
  assert (x == Seq.index (as_rseq b (mk_rmem (array_resource b) h0)) (UInt32.v i));
  x

#pop-options

let index #a b i = RST?.reflect (index_ #a b i)

let upd (#a:Type) (b:A.array a) (i:UInt32.t) (v:a) =
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  (**) let h0 = HST.get () in
  A.upd b i v;
  (**) let h1 = HST.get () in
  (**) assert(modifies (array_resource b) (array_resource b) h0 h1);
  (**) assert(A.loc_includes (A.loc_used_in h0) (as_loc (fp (array_resource b)) h0));
  (**) A.live_array_used_in b h1;
  (**) same_perm_seq_always_constant h0 h1 b

let alloc (#a:Type) (init:a) (len:UInt32.t) =
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  let b = A.alloc init len in
  (**) let h1 = HST.get () in
  (**) assert(forall (i:nat{i < A.vlength #a b}). A.get_perm #a h1 b i == P.full_permission);
  // Find out how to trigger that
  (**) A.live_array_used_in b h1;
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
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in b h1;
  b'


let gather #a b b' =
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  (**) reveal_star();
  A.gather #a b b';
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in b h1

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
  (**)   assert(A.get_perm h1 b1 i == A.get_perm h0 b i);
  (**)   assert(A.get_perm h1 b1 j == A.get_perm h0 b j)
  (**) in
  (**) Classical.forall_intro_2 aux1;
  (**) let aux2 (i:nat{i < A.vlength b2}) (j:nat{j < A.vlength b2}) : Lemma (A.get_perm h1 b2 i == A.get_perm h1 b2 j) =
  (**)   assert(A.get_perm h1 b2 i == A.get_perm h0 b (i + A.vlength b1));
  (**)   assert(A.get_perm h1 b2 j == A.get_perm h0 b (j + A.vlength b1))
  (**) in
  (**) Classical.forall_intro_2 aux2;
  (**) assert(forall(i:nat{i < A.vlength b2}). (A.get_perm h1 b2 i == A.get_perm h0 b (i + A.vlength b1)));
  (**) A.loc_union_is_split_into #a b b1 b2;
  (b1, b2)

#push-options "--z3rlimit 10"

let glue #a b b1 b2 =
  (**) assert(A.is_split_into b (b1,b2));
  (**) reveal_array ();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  (**) let h0 = HST.get () in
  (**) reveal_star_inv (array_resource b1) (array_resource b2) h0;
  A.glue #a b b1 b2;
  (**) let h1 = HST.get () in
  (**) let aux (i:nat{i < A.vlength b}) (j:nat{j < A.vlength b}) : Lemma (A.get_perm h1 b i == A.get_perm h1 b j) =
  (**)   begin if i < A.vlength b1 then
  (**)     assert(A.get_perm h1 b i == A.get_perm h0 b1 i)
  (**)   else
  (**)     assert(A.get_perm h1 b i == A.get_perm h0 b2 (i - A.vlength b1))
  (**)   end;
  (**)   if j < A.vlength b1 then
  (**)     assert(A.get_perm h1 b j == A.get_perm h0 b1 j)
  (**)   else
  (**)     assert(A.get_perm h1 b j == A.get_perm h0 b2 (j - A.vlength b1))
  (**) in
  (**) Classical.forall_intro_2 aux;
  (**) assert(A.modifies A.loc_none h0 h1);
  (**) A.loc_includes_none (A.loc_array b);
  (**) assert(A.modifies (A.loc_array b) h0 h1);
  (**) assert(A.is_split_into b (b1,b2));
  (**) A.loc_union_is_split_into b b1 b2

#pop-options

let copy #a o i = admit()
