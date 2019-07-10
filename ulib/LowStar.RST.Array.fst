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

friend LowStar.Array

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
  (**)     assert(A.get_perm h1 b i = A.get_perm h0 b1 i)
  (**)   else
  (**)     assert(A.get_perm h1 b i = A.get_perm h0 b2 (i - A.vlength b1))
  (**)   end;
  (**)   if j < A.vlength b1 then
  (**)     assert(A.get_perm h1 b j = A.get_perm h0 b1 j)
  (**)   else
  (**)     assert(A.get_perm h1 b j = A.get_perm h0 b2 (j - A.vlength b1))
  (**) in
  (**) Classical.forall_intro_2 aux;
  (**) assert(A.modifies A.loc_none h0 h1);
  (**) A.loc_includes_none (A.loc_array b);
  (**) assert(A.modifies (A.loc_array b) h0 h1);
  (**) assert(A.is_split_into b (b1,b2));
  (**) A.loc_union_is_split_into b b1 b2

#pop-options



abstract
let full_array_view (#a:Type) (b:A.array a) : view (varray a) =
  reveal_view ();
  let fp = Ghost.hide (A.loc_freed_mreference b.A.content) in
  let inv h =
    A.live h b /\ constant_perm_seq h b
  in
  let sel (h: HS.mem) : GTot (varray a) = { s = A.as_seq h b; p = A.get_perm h b 0 } in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }


let full_array_resource (#a:Type) (b:A.array a) =
  as_resource (full_array_view b)

let promote (#a:Type) (b:A.array a) : RST unit
  (full_array_resource b)
  (fun _ -> array_resource b)
  (fun _ -> True)
  (fun _ _ _ -> True)
  = 
  let h0 = HST.get() in
  reveal_array();
  reveal_rst_inv();
  reveal_modifies();
  // assume     (forall frame .
  //     A.loc_disjoint frame (A.loc_array b) /\
  //     A.loc_includes (A.loc_not_unused_in h0) frame
  //     ==>
  //     A.loc_disjoint frame (A.loc_freed_mreference b.A.content) /\
  //     A.loc_includes (A.loc_not_unused_in h0) frame);

//  assume (modifies (array_resource b) (full_array_resource b) h0 h0);
  ()

let test (#a:Type) (b:A.array a) (v:a): RST unit
  (full_array_resource b)
  (fun _ -> full_array_resource b)
  (fun h0 -> P.allows_write (sel (full_array_view b) h0).p)
  (fun _ _ _ -> True)
  =
  reveal_array();
  reveal_rst_inv();
  reveal_modifies();
  upd b 0ul v;
  ()

assume
val arr_free (#a: Type) (b: A.array a) : HST.ST unit
  (requires (fun h0 -> A.writeable h0 b /\ A.live  h0 b /\ A.freeable b))
  (ensures (fun h0 _ h1 ->
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
    (HS.get_tip h1) == (HS.get_tip h0) /\
    A.modifies (A.loc_freed_mreference b.A.content) h0 h1 /\
    HS.live_region h1 (A.frameOf b)
  ))

let full_free (#a:Type) (b:A.array a)
  : RST unit (full_array_resource b)
             (fun _ -> empty_resource)
             (fun h0 -> A.freeable b /\ P.allows_write (sel (array_view b) h0).p)
             (fun _ _ _ -> True)
  =  (**) reveal_array();
  (**) reveal_empty_resource();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  arr_free b

val arr_alloc (#a:Type0) (init:a) (len:UInt32.t)
  : ST (A.array a)
       (requires fun _ -> UInt32.v len > 0)
       (ensures fun h0 b h1 ->
         A.modifies A.loc_none h0 h1 /\
         A.fresh_loc (A.loc_freed_mreference b.A.content) h0 h1 /\
         A.writeable h1 b /\
         A.freeable b /\
         A.as_seq h1 b == Seq.create (UInt32.v len) init)

let arr_alloc #a init len =
  let perm_map_pid = Ghost.hide (
    let (vp, pid) = LowStar.Permissions.new_value_perms init true in
    ((vp <: LowStar.Permissions.perms_rec a), Ghost.hide pid)
  ) in
  let v = (init, Ghost.hide (fst (Ghost.reveal perm_map_pid))) in
  let s = Seq.create (UInt32.v len) v in
  (**) let h0 = HST.get() in
  let content = HST.ralloc_mm HS.root s in
  (**) let h1 = HST.get() in
  (**) MG.modifies_ralloc_post #A.ucell #A.cls HS.root s h0 content h1;
  let b = A.Array len content 0ul len (snd (Ghost.reveal perm_map_pid)) in
  (**) assert (Seq.equal (A.as_seq h1 b) (Seq.create (UInt32.v len) init));
  b

let full_alloc (#a:Type) (init:a) (len:UInt32.t)
  : RST (A.array a)
        (empty_resource)
        (fun b -> full_array_resource b)
        (fun _ -> UInt32.v len > 0)
        (fun _ b h1 ->
        A.freeable b /\
        (sel (array_view b) h1).s == Seq.create (UInt32.v len) init /\
        (sel (array_view b) h1).p = FStar.Real.one
        )
  =   (**) reveal_array();
  (**) reveal_rst_inv();
  (**) reveal_modifies();
  let b = arr_alloc init len in
  // (**) let h1 = HST.get () in
  // (**) assert(forall (i:nat{i < A.vlength #a b}). A.get_perm #a h1 b i = FStar.Real.one); // Find out how to trigger that
  // (**) A.loc_includes_adresses_loc_array #a b true;
  b

let frame_full_pre (#a:Type) (b:A.array a) (res:resource) (pre:r_pre (array_resource b <*> res)) 
  (h:imem (inv (full_array_resource b <*> res)))
  = 
  reveal_array();
  reveal_star();
  pre h /\
  sel (array_view b) h == sel (full_array_view b) h

let frame_full_post(#t:Type)
                   (#a:Type) 
                   (b:A.array a)
                   (res0:resource) 
                   (res1:t -> resource)
                   (pre:r_pre (array_resource b <*> res0)) 
                   (post:r_post (array_resource b <*> res0) t (fun x -> array_resource b <*> res1 x))
                   (h0:imem (inv (full_array_resource b <*> res0)))
                   (x:t)
                   (h1:imem (inv (full_array_resource b <*> res1 x)))
    = reveal_array();
      reveal_star();
      post h0 x h1 /\
      sel (array_view b) h1 == sel (full_array_view b) h1

let frame_full_array (#t:Type) (#a:Type) (b:A.array a)
    (res0:resource)
    (res1:t -> resource)
    (#pre:r_pre (array_resource b <*> res0))
    (#post:r_post (array_resource b <*> res0) t (fun x -> array_resource b <*> res1 x))
    ($f:unit -> RST t (array_resource b <*> res0) (fun x -> array_resource b <*> res1 x) pre post) 
    : RST t
      (full_array_resource b <*> res0)
      (fun x -> full_array_resource b <*> res1 x)
      (frame_full_pre b res0 pre)
      (frame_full_post b res0 res1 pre post)
   = reveal_modifies();
     reveal_rst_inv();
     reveal_array();
     reveal_star();
     let h0 = HST.get() in
     let x = f() in
     let h1 = HST.get() in
     A.loc_includes_disjoint_elim (as_loc (fp (res1 x))) (A.loc_array b) (A.loc_union (as_loc (fp res0)) (A.loc_unused_in h0));
     A.unused_in_not_unused_in_disjoint_2 (A.loc_unused_in h0) (A.loc_not_unused_in h0) (A.loc_unused_in h0) (A.loc_not_unused_in h0) h0;
     x
