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

let index_ (#a:Type) (b:A.array a) (i:UInt32.t) = fun _ ->
  (**) reveal_array ();
  (**) let h0 = HST.get () in
  let x = A.index b i in
  (**) // TODO: how to trigger that automatically ?
  (**) assert((mk_rmem (array_resource b) h0) (array_resource b) == sel_of (array_resource b).view h0);
  x

let index #a b i = RST?.reflect (index_ #a b i)

val upd_ (#a:Type) (b:A.array a) (i:UInt32.t) (v:a)
  : rst_repr unit (array_resource b)
    (fun _ -> array_resource b)
    (fun h0 -> UInt32.v i < A.vlength b /\ P.allows_write (get_rperm b h0))
    (fun h0 _ h1 -> UInt32.v i < A.vlength b /\
      as_rseq b h1 ==
      Seq.upd (as_rseq b h0) (UInt32.v i) v /\
      get_rperm b h1 == get_rperm b h0
    )

let upd_ (#a:Type) (b:A.array a) (i:UInt32.t) (v:a) = fun _ ->
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  (**) let h0 = HST.get () in
  A.upd b i v;
  (**) let h1 = HST.get () in
  (**) assert(modifies (array_resource b) (array_resource b) h0 h1);
  (**) assert(A.loc_includes (A.loc_used_in h0) (as_loc (fp_of (array_resource b)) h0));
  (**) A.live_array_used_in b h1;
  (**) same_perm_seq_always_constant h0 h1 b;
  (**) assert((mk_rmem (array_resource b) h0) (array_resource b) ==
  (**)   sel_of (array_resource b).view h0);
  (**) assert((mk_rmem (array_resource b) h1) (array_resource b) ==
  (**)   sel_of (array_resource b).view h1)

let upd #a b i v = RST?.reflect (upd_ #a b i v)

val alloc_ (#a:Type) (init:a) (len:UInt32.t)
  : rst_repr (A.array a)
    (empty_resource)
    (fun b -> array_resource b)
    (fun _ -> UInt32.v len > 0)
    (fun _ b h1 ->
      A.freeable b /\
      as_rseq b h1 == Seq.create (UInt32.v len) init /\
      get_rperm b h1 == P.full_permission /\
      A.vlength b = UInt32.v len
    )

let alloc_ (#a:Type) (init:a) (len:UInt32.t) = fun _ ->
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  let b = A.alloc init len in
  (**) let h1 = HST.get () in
  (**) assert(forall (i:nat{i < A.vlength #a b}). A.get_perm #a h1 b i == P.full_permission);
  // TODO: Find out how to trigger that
  (**) A.live_array_used_in b h1;
  (**) assert((mk_rmem (array_resource b) h1) (array_resource b) ==
  (**)  sel_of (array_resource b).view h1);
  b

let alloc #a init len = RST?.reflect (alloc_ #a init len)

val free_ (#a:Type) (b:A.array a)
  : rst_repr unit (array_resource b)
    (fun _ -> empty_resource)
    (fun h0 -> A.freeable b /\ P.allows_write (get_rperm b h0))
    (fun _ _ _ -> True)

let free_ (#a:Type) (b:A.array a) = fun _ ->
  (**) reveal_array();
  (**) reveal_empty_resource();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  (**) let h0 = HST.get () in
  (**) assert((mk_rmem (array_resource b) h0) (array_resource b) ==
  (**)   sel_of (array_resource b).view h0);
  A.free b;
  (**) let h1 = HST.get () in
  (**) assert((mk_rmem empty_resource h1) empty_resource == sel_of empty_resource.view h1)

let free #a b = RST?.reflect (free_ #a b)

val share_ (#a:Type) (b:A.array a)
  : rst_repr (A.array a)
        (array_resource b)
        (fun b' -> array_resource b <*> array_resource b')
        (fun _ -> A.vlength b > 0)
        (fun h0 b' h1 ->
          A.vlength b' = A.vlength b /\
          as_rseq b h0 == as_rseq b h1 /\
          as_rseq b' h1 == as_rseq b h1 /\
          get_rperm b h1 == P.half_permission (get_rperm b h0) /\
          get_rperm b' h1  == P.half_permission (get_rperm b h0) /\
          summable_permissions b b' h1
        )

let share_ #a b = fun _ ->
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  (**) reveal_star();
  (**) let h0 = HST.get () in
  let b' = A.share b in
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in b h1;
  (**) assert((mk_rmem (array_resource b) h0) (array_resource b) ==
  (**)   sel_of (array_resource b).view h0);
  (**) assert(
  (**)   (mk_rmem (array_resource b <*> array_resource b') h1)
  (**)     (array_resource b <*> array_resource b') ==
  (**)   sel_of (array_resource b <*> array_resource b').view h1
  (**) );
  b'

let share #a b = RST?.reflect (share_ #a b)

val gather_ (#a:Type) (b b':A.array a)
  : rst_repr unit (array_resource b <*> array_resource b')
    (fun _ -> array_resource b)
    (fun h0 -> A.gatherable b b' /\ summable_permissions b b' h0)
    (fun h0 _ h1 ->
      summable_permissions b b' h0 /\
      as_rseq b h0 == as_rseq b h1 /\
      get_rperm b h1 == P.sum_permissions (get_rperm b h0) (get_rperm b' h0)
    )

let gather_ #a b b' = fun _ ->
  (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  (**) reveal_star();
  (**) let h0 = HST.get () in
  A.gather #a b b';
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in b h1;
  (**) assert((mk_rmem (array_resource b) h1) (array_resource b) == sel_of (array_resource b).view h1);
  (**) assert(
  (**)   (mk_rmem (array_resource b <*> array_resource b') h0)
  (**)     (array_resource b <*> array_resource b') ==
  (**)   sel_of (array_resource b <*> array_resource b').view h0
  (**) )

let gather #a b b' = RST?.reflect (gather_ #a b b')

val split_ (#a: Type) (b: A.array a) (idx: UInt32.t)
  : rst_repr (A.array a & A.array a)
    (array_resource b)
    (fun p -> array_resource (fst p) <*> array_resource (snd p))
    (fun _ -> UInt32.v idx > 0 /\ UInt32.v idx < A.vlength b)
    (fun h0 bs h1 ->
      UInt32.v idx > 0 /\ UInt32.v idx < A.vlength b /\
      A.is_split_into b (fst bs, snd bs) /\
      as_rseq (fst bs) h1 == Seq.slice (as_rseq b h0) 0 (UInt32.v idx) /\
      as_rseq (snd bs) h1 == Seq.slice (as_rseq b h0) (UInt32.v idx) (A.vlength b) /\
      A.vlength (fst bs) = UInt32.v idx /\
      A.vlength (snd bs) = A.vlength b - UInt32.v idx /\
      get_rperm (fst bs) h1 == get_rperm b h0 /\
      get_rperm (snd bs) h1 == get_rperm b h0
    )

let split_ #a b idx = fun _ ->
  (**) reveal_array ();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  (**) let h0 = HST.get () in
  let (b1, b2) = A.split #a b idx in
  (**) let h1 = HST.get () in
  (**) reveal_star_inv (array_resource b1) (array_resource b2) h1;
  (**) let aux1 (i:nat{i < A.vlength b1}) (j:nat{j < A.vlength b1})
  (**)   : Lemma (A.get_perm h1 b1 i == A.get_perm h1 b1 j) =
  (**)   assert(A.get_perm h1 b1 i == A.get_perm h0 b i);
  (**)   assert(A.get_perm h1 b1 j == A.get_perm h0 b j)
  (**) in
  (**) Classical.forall_intro_2 aux1;
  (**) let aux2 (i:nat{i < A.vlength b2}) (j:nat{j < A.vlength b2})
  (**)   : Lemma (A.get_perm h1 b2 i == A.get_perm h1 b2 j) =
  (**)   assert(A.get_perm h1 b2 i == A.get_perm h0 b (i + A.vlength b1));
  (**)   assert(A.get_perm h1 b2 j == A.get_perm h0 b (j + A.vlength b1))
  (**) in
  (**) Classical.forall_intro_2 aux2;
  (**) assert(forall(i:nat{i < A.vlength b2}). (A.get_perm h1 b2 i ==
  (**)   A.get_perm h0 b (i + A.vlength b1)));
  (**) A.loc_union_is_split_into #a b b1 b2;
  (**) assert((mk_rmem (array_resource b) h0) (array_resource b) ==
  (**)   sel_of (array_resource b).view h0);
  (**) assert(
  (**)   (mk_rmem (array_resource b1 <*> array_resource b2) h1)
  (**)     (array_resource b1 <*> array_resource b2) ==
  (**)   sel_of (array_resource b1 <*> array_resource b2).view h1
  (**) );
  (b1, b2)

#push-options "--z3rlimit 10"

let split #a b idx = RST?.reflect (split_ #a b idx)

val glue_ (#a: Type) (b b1 b2: A.array a)
  : rst_repr unit
    (array_resource b1 <*> array_resource b2)
    (fun _ -> array_resource b)
    (fun h0 -> A.is_split_into b (b1, b2) /\ get_rperm b1 h0 == get_rperm b2 h0)
    (fun h0 _ h1 ->
      as_rseq b h1 == Seq.append (as_rseq b1 h0) (as_rseq b2 h0) /\
      get_rperm b h1 == get_rperm b1 h0
    )

let glue_ #a b b1 b2 = fun _ ->
  (**) assert(A.is_split_into b (b1,b2));
  (**) reveal_array ();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  (**) let h0 = HST.get () in
  (**) reveal_star_inv (array_resource b1) (array_resource b2) h0;
  A.glue #a b b1 b2;
  (**) let h1 = HST.get () in
  (**) let aux (i:nat{i < A.vlength b}) (j:nat{j < A.vlength b})
  (**)   : Lemma (A.get_perm h1 b i == A.get_perm h1 b j) =
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
  (**) A.loc_union_is_split_into b b1 b2;
  (**) assert((mk_rmem (array_resource b) h1) (array_resource b) ==
  (**)   sel_of (array_resource b).view h1);
  (**) assert(
  (**)   (mk_rmem (array_resource b1 <*> array_resource b2) h0)
  (**)     (array_resource b1 <*> array_resource b2) ==
  (**)   sel_of (array_resource b1 <*> array_resource b2).view h0
  (**) )

#pop-options

let glue #a b b1 b2 = RST?.reflect (glue_ #a b b1 b2)

let copy #a o i = admit()
