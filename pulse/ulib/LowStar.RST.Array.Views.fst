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
module LowStar.RST.Array.Views

open FStar.HyperStack.ST
module A = LowStar.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module P = LowStar.Permissions
module MG = FStar.ModifiesGen
module U32 = FStar.UInt32

open LowStar.Resource
open LowStar.RST

noeq type varray (#a: Type) (b: A.array a) = {
  s: Seq.lseq a (A.vlength b);
  p: Ghost.erased P.permission
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

#set-options "--z3rlimit 20"

abstract
let array_view (#a:Type) (b:A.array a) : Tot (view (varray b)) =
  reveal_view ();
  let fp = Ghost.hide (A.loc_array b) in
  let inv (h: HS.mem) : prop =
    A.live h b /\ constant_perm_seq h b
  in
  let sel (h: HS.mem) : GTot (varray b) = { s = A.as_seq h b; p = Ghost.hide (A.get_perm h b 0) } in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

unfold let array_resource (#a:Type) (b:A.array a) : Tot resource =
  as_resource (array_view b)

let as_seq
  (#a: Type)
  (b: A.array a)
  (#r: resource{array_resource #a b `is_subresource_of` r})
  (h: rmem r) : GTot (Seq.lseq a (A.vlength b))  =
  (h (array_resource b)).s

let get_perm
  (#a: Type)
  (b: A.array a)
  (#r: resource{array_resource #a b `is_subresource_of` r})
  (h: rmem r) : GTot P.permission =
  Ghost.reveal (h (array_resource b)).p

let reveal_array ()
  : Lemma (
    (forall a (b:A.array a) .{:pattern as_loc (fp (array_resource b))}
      as_loc (fp (array_resource b)) == A.loc_array b) /\
      (forall a (b:A.array a) h .{:pattern inv (array_resource b) h}
        inv (array_resource b) h <==> A.live h b /\ constant_perm_seq h b
      ) /\
      (forall a (b:A.array a) h .{:pattern sel (array_view b) h}
        sel (array_view b) h == { s = A.as_seq h b; p = Ghost.hide (A.get_perm h b 0) }
      )
    ) =
  ()


let summable_permissions (#a:Type) (b:A.array a) (b':A.array a) (h: rmem (array_resource b <*> array_resource b')) =
  A.gatherable b b' /\
  P.summable_permissions (get_perm b h) (get_perm b' h)
