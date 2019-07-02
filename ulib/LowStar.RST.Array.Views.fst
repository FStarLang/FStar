module LowStar.RST.Array.Views

open FStar.HyperStack.ST
module A = LowStar.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module P = LowStar.Permissions
module MG = FStar.ModifiesGen

open LowStar.Resource
open LowStar.RST

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
        inv (array_resource b) h <==> A.live h b /\ constant_perm_seq h b
      ) /\
      (forall a (b:A.array a) h .{:pattern sel (array_view b) h}
        sel (array_view b) h == { s = A.as_seq h b; p = A.get_perm h b 0 }
      )
    ) =
  ()

val length_view_as_seq (#a:Type) (h:HS.mem) (b:A.array a) : Lemma
  (requires (array_view b).inv h)
  (ensures A.vlength b == Seq.length (sel (array_view b) h).s)
  [SMTPat (sel (array_view b) h).s]

let length_view_as_seq #a h b = ()

let summable_permissions (#a:Type) (h:HS.mem) (b:A.array a{(array_view b).inv h}) (b':A.array a{(array_view b').inv h}) =
  A.mergeable b b' /\
  P.summable_permissions (sel (array_view b) h).p (sel (array_view b') h).p
