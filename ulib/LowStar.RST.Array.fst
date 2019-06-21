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

open FStar.HyperStack.ST
module A = LowStar.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module P = LowStar.Permissions
module MG = FStar.ModifiesGen

open LowStar.Resource
open LowStar.RST

open LowStar.BufferOps

type varray (a: Type) = {
  s: Seq.seq a;
  p: P.permission
}

let constant_perm_seq (#a: Type) (h: HS.mem) (b: A.array a) : Type =
  (forall (i:nat{i < A.vlength b}) (j:nat{j < A.vlength b}). {:pattern (A.get_perm h b i); (A.get_perm h b j) }
      A.get_perm h b i == A.get_perm h b j // Array resource cells have uniform permissions
  )

let same_perm_seq_always_constant (#a: Type) (h0 h1: HS.mem) (b:A.array a) : Lemma
  (requires (A.as_perm_seq h0 b == A.as_perm_seq h1 b /\ constant_perm_seq h0 b))
  (ensures (constant_perm_seq h1 b))
  [SMTPat (constant_perm_seq h1 b); SMTPat (constant_perm_seq h0 b)]
  =
  let aux (i:nat{i < A.vlength b}) (j:nat{j < A.vlength b}) : Lemma ( A.get_perm h1 b i == A.get_perm h1 b j) =
    assert(A.get_perm h0 b i == A.get_perm h0 b j)
  in
  Classical.forall_intro_2 aux

abstract
let array_view (#a:Type) (b:A.array a) : view (varray a) =
  reveal_view ();
  let fp = Ghost.hide (A.loc_array b) in
  let inv h =
    A.live h b /\ constant_perm_seq h b
  in
  let sel (h: imem inv) : GTot (varray a) = { s = A.as_seq h b; p = A.get_perm h b 0 } in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

let array_resource (#a:Type) (b:A.array a) =
  as_resource (array_view b)

let reveal_array ()
  : Lemma (
    (forall a (b:A.array a) .{:pattern as_loc (fp (array_resource b))}
      as_loc (fp (array_resource b)) == A.loc_array b) /\
      (forall a (b:A.array a) h .{:pattern inv (array_resource b) h}
        inv (array_resource b) h <==> A.live h b /\
        (forall (i:nat{i < A.vlength b}) (j:nat{j < A.vlength b}). {:pattern (A.get_perm h b i); (A.get_perm h b j) }
          A.get_perm h b i == A.get_perm h b j // Array resource cells have uniform permissions
        )
      ) /\
      (forall a (b:A.array a) h .{:pattern sel (array_view b) h}
        sel (array_view b) h == { s = A.as_seq h b; p = A.get_perm h b 0 }
      )
    ) =
  ()

let index (#a:Type) (b:A.array a) (i:UInt32.t)
  : RST a (array_resource b)
    (fun _ -> array_resource b)
    (fun h0 -> UInt32.v i < A.vlength b /\ P.allows_read (sel (array_view b) h0).p)
    (fun h0 x h1 ->
      UInt32.v i < A.vlength b /\
      Seq.index (sel (array_view b) h0).s (UInt32.v i) == x /\
      sel (array_view b) h0 == sel (array_view b) h1
    )
  = A.index b i

let upd (#a:Type) (b:A.array a) (i:UInt32.t) (v:a)
  : RST unit (array_resource b)
    (fun _ -> array_resource b)
    (fun h0 -> UInt32.v i < A.vlength b /\ P.allows_write (sel (array_view b) h0).p )
    (fun h0 _ h1 -> UInt32.v i < A.vlength b /\
      (sel (array_view b) h1).s ==
         Seq.upd (sel (array_view b) h0).s (UInt32.v i) v /\
      (sel (array_view b) h1).p == (sel (array_view b) h0).p
     )
  =
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


let alloc (#a:Type) (init:a) (len:UInt32.t)
  : RST (A.array a)
    (empty_resource)
    (fun b -> array_resource b)
    (fun _ -> UInt32.v len > 0)
    (fun _ b h1 ->
      (sel (array_view b) h1).s == Seq.create (UInt32.v len) init /\
      (sel (array_view b) h1).p = FStar.Real.one
    )
  =
  reveal_rst_inv();
  reveal_modifies();
  let b = A.alloc init len in
  (**) let h1 = HST.get () in
  assert(forall (i:nat{i < A.vlength #a b}). A.get_perm #a h1 b i = FStar.Real.one); // Find out how to trigger that
  A.loc_includes_adresses_loc_array #a b true;
  b

let free (#a:Type) (b:A.array a)
  : RST unit (array_resource b)
             (fun _ -> empty_resource)
             (fun h0 -> A.freeable b /\ P.allows_write (sel (array_view b) h0).p)
             (fun _ _ _ -> True)
   =
   reveal_empty_resource();
   reveal_rst_inv();
   reveal_modifies();
   A.free b
