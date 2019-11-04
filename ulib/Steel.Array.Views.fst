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
module Steel.Array.Views

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module P = LowStar.Permissions
module MG = FStar.ModifiesGen
module U32 = FStar.UInt32

open Steel.RST

include LowStar.Array

noeq type varray (#a: Type) (b: array a) = {
  s: Seq.lseq a (vlength b);
  p: P.permission
}

/// Array resource cells have uniform permissions
let constant_perm_seq (#a: Type) (h: HS.mem) (b: array a) =
  (forall (i:nat{i < vlength b}) (j:nat{j < vlength b}).
      get_perm h b i == get_perm h b j
  )

let constant_perm_seq_elim
  (#a: Type)
  (h: HS.mem)
  (b: array a)
  (i:nat{i < vlength b})
  (j:nat{j < vlength b})
  : Lemma
    (requires (constant_perm_seq #a h b))
    (ensures (get_perm h b i == get_perm h b j))
  = ()

let constant_perm_seq_intro
  (#a: Type)
  (h: HS.mem)
  (b: array a)
  (lemma: (i:nat{i < vlength b}) -> (j:nat{j < vlength b}) -> Lemma
    (ensures (get_perm h b i == get_perm h b j))
  ) : Lemma
    (constant_perm_seq #a h b)
  =
  let aux (i:nat{i < vlength b}) (j:nat{j < vlength b}) : Lemma (get_perm h b i == get_perm h b j) =
    lemma i j
  in
  Classical.forall_intro_2 aux

let constant_perm_seq_preserved_by_sub (#a: Type) (h: HS.mem) (b: array a)
  (start:U32.t) (len:U32.t{U32.v len > 0}) : Lemma
    (requires (U32.v start + U32.v len <= vlength b) /\ constant_perm_seq #a h b)
    (ensures (constant_perm_seq #a h (gsub b start len)))
    [SMTPat (constant_perm_seq #a h (gsub b start len))]
  =
  let b' : array a = gsub b start len in
  constant_perm_seq_intro #a h b' (fun i j ->
    assert(get_perm h b' i == get_perm h b U32.(i + v start));
    assert(get_perm h b' j == get_perm h b U32.(j + v start))
  )

let same_perm_seq_always_constant (#a: Type) (h0 h1: HS.mem) (b:array a) : Lemma
  (requires (as_perm_seq h0 b == as_perm_seq h1 b /\ constant_perm_seq h0 b))
  (ensures (constant_perm_seq h1 b))
  [SMTPat (constant_perm_seq h1 b); SMTPat (constant_perm_seq h0 b)]
  =
  let aux (i:nat{i < vlength b}) (j:nat{j < vlength b}) : Lemma ( get_perm h1 b i == get_perm h1 b j) =
    assert(get_perm h0 b i == get_perm h0 b j)
  in
  Classical.forall_intro_2 aux

#set-options "--z3rlimit 20"

abstract
let array_view (#a:Type) (b:array a) : Tot (view (varray b)) =
  reveal_view ();
  let fp (h: HS.mem) = loc_array b in
  let inv (h: HS.mem) : prop =
    live h b /\ constant_perm_seq h b
  in
  let sel (h: HS.mem) : GTot (varray b) = { s = as_seq h b; p = get_perm h b 0 } in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

let array_resource (#a:Type) (b:array a) : Tot resource =
  as_resource (array_view b)

let as_rseq
  (#a: Type)
  (b: array a)
  (#r: resource{array_resource #a b `is_subresource_of` r})
  (h: rmem r) : GTot (Seq.lseq a (vlength b)) =
  (h (array_resource b)).s

let get_rperm
  (#a: Type)
  (b: array a)
  (#r: resource{array_resource #a b `is_subresource_of` r})
  (h: rmem r) : GTot P.permission  =
  (h (array_resource b)).p

let reveal_array ()
  : Lemma (
    (forall a (b:array a) h .{:pattern as_loc (fp (array_resource b)) h}
      as_loc (fp (array_resource b)) h == loc_array b) /\
      (forall a (b:array a) h .{:pattern inv (array_resource b) h}
        inv (array_resource b) h <==> live h b /\ constant_perm_seq h b
      ) /\
      (forall a (b:array a) h .{:pattern sel (array_view b) h}
        sel (array_view b) h == { s = as_seq h b; p = get_perm h b 0 }
      )
    ) =
  ()


let summable_permissions
  (#a:Type)
  (b:array a)
  (b':array a)
  (h: rmem (array_resource b <*> array_resource b')) =
  gatherable b b' /\
  P.summable_permissions (get_rperm b h) (get_rperm b' h)
