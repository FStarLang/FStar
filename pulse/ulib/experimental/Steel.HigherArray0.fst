module Steel.HigherArray0

module R = Steel.PCMReference
module P = Steel.PCMFrac
module M = FStar.Map
module PM = Steel.PCMMap
module U32 = FStar.UInt32

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

/// NOTE: This module is slated to have primitive Karamel extraction.

[@@noextract_to "krml"]
let index_t (len: Ghost.erased nat) : Tot Type0 =
  (i: nat { i < len })

[@@noextract_to "krml"]
let carrier (elt: Type u#a) (len: Ghost.erased nat) : Tot Type =
  PM.map (index_t len) (P.fractional elt)

[@@noextract_to "krml"]
let pcm (elt: Type u#a) (len: Ghost.erased nat) : Tot (P.pcm (carrier elt len)) =
  PM.pointwise (index_t len) (P.pcm_frac #elt)

[@@noextract_to "krml"]
let one (#elt: Type) (#len: Ghost.erased nat) = (pcm elt len).P.p.P.one
let composable (#elt: Type) (#len: Ghost.erased nat) = (pcm elt len).P.p.P.composable
[@@noextract_to "krml"]
let compose (#elt: Type) (#len: Ghost.erased nat) = (pcm elt len).P.p.P.op

[@@noextract_to "krml"]
let mk_carrier
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p: P.perm)
: Tot (carrier elt len)
= let f (i: nat) : Tot (P.fractional elt) =
    if offset + Seq.length s > len || i < offset || i >= offset + Seq.length s
    then None
    else Some (Seq.index s (i - offset), p)
  in
  M.map_literal f

let mk_carrier_inj
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s1 s2: Seq.seq elt)
  (p1 p2: P.perm)
: Lemma
  (requires (
    mk_carrier len offset s1 p1 == mk_carrier len offset s2 p2 /\
    offset + Seq.length s1 <= len /\
    offset + Seq.length s2 <= len
  ))
  (ensures (
    s1 `Seq.equal` s2 /\
    (Seq.length s1 > 0 ==> p1 == p2)
  ))
= assert (forall (i: nat) . i < Seq.length s1 ==>
    (M.sel (mk_carrier len offset s1 p1) (offset + i) == Some (Seq.index s1 i, p1)));
  assert (forall (i: nat) . i < Seq.length s2 ==>
     M.sel (mk_carrier len offset s2 p2) (offset + i) == Some (Seq.index s2 i, p2))

[@@noextract_to "krml"]
noeq
type ptr (elt: Type) = {
  base_len: Ghost.erased U32.t;
                   // U32.t to prove that A.read, A.write offset computation does not overflow. TODO: replace U32.t with size_t
  base: ref _ (pcm elt (U32.v base_len));
  offset: (offset: nat { offset <= U32.v base_len });
}

[@@erasable]
let base_t (elt: Type) : Tot Type = Ghost.erased (base_len: U32.t & ref _ (pcm elt (U32.v base_len)))
let base_len (#elt: Type) (b: base_t elt) : GTot nat = U32.v (dfst b)
let base (#elt: Type) (p: ptr elt) : Tot (base_t elt) = (| Ghost.reveal p.base_len, p.base |)
let offset (#elt: Type) (p: ptr elt) : Ghost nat (requires True) (ensures (fun offset -> offset <= base_len (base p))) = p.offset

let ptr_base_offset_inj (#elt: Type) (p1 p2: ptr elt) : Lemma
  (requires (
    base p1 == base p2 /\
    offset p1 == offset p2
  ))
  (ensures (
    p1 == p2
  ))
= ()

inline_for_extraction // this will extract to ptr, erasing the length field
[@@noextract_to "krml"]
noeq
type array (elt: Type) = {
  p: ptr elt;
  length: (length: Ghost.erased nat {offset p + length <= base_len (base p)});
}

let length (#elt: Type) (a: array elt) : GTot nat =
  a.length

let len (#elt: Type) (a: array elt) : GTot U32.t =
  U32.uint_to_t (length a)

let valid_perm
  (len: nat)
  (offset: nat)
  (slice_len: nat)
  (p: P.perm) : Tot prop =
  let open FStar.Real in
  ((offset + slice_len <= len /\ slice_len > 0) ==> (p.P.v <=. one))

[@__reduce__]
let pts_to0 (#elt: Type u#1) (a: array elt) (p: P.perm) (s: Seq.seq elt) : Tot vprop =
  R.pts_to a.p.base (mk_carrier (U32.v a.p.base_len) a.p.offset s p) `star`
  pure (
    valid_perm (U32.v a.p.base_len) a.p.offset (Seq.length s) p /\
    Seq.length s == length a
  )

let pts_to (#elt: Type u#1) (a: array elt) ([@@@ smt_fallback ] p: P.perm) ([@@@ smt_fallback ] s: Seq.seq elt) : Tot vprop =
  pts_to0 a p s

// this lemma is necessary because Steel.PCMReference is marked unfold
let change_r_pts_to
  (#opened: _)
  (#carrier: Type u#1)
  (#pcm: P.pcm carrier)
  (p: ref carrier pcm)
  (v: carrier)
  (#carrier': Type u#1)
  (#pcm': P.pcm carrier')
  (p': ref carrier' pcm')
  (v': carrier')
: SteelGhost unit opened
    (R.pts_to p v)
    (fun _ -> R.pts_to p' v')
    (fun _ ->  // keep on distinct lines for error messages
      carrier == carrier' /\
      pcm == pcm' /\
      p == p' /\
      v == v')
    (fun _ _ _ -> True)
= change_equal_slprop
    (R.pts_to p v)
    (R.pts_to p' v')

let intro_pts_to (#opened: _) (#elt: Type u#1) (a: array elt) (#v: _) (p: P.perm) (s: Seq.seq elt) : SteelGhost unit opened
  (R.pts_to a.p.base v)
  (fun _ -> pts_to a p s)
  (fun _ ->
    v == mk_carrier (U32.v a.p.base_len) a.p.offset s p /\
    valid_perm (U32.v a.p.base_len) a.p.offset (Seq.length s) p /\
    Seq.length s == length a
  )
  (fun _ _ _ -> True)
= change_r_pts_to a.p.base v a.p.base (mk_carrier (U32.v a.p.base_len) a.p.offset s p);
  intro_pure _;
  change_equal_slprop
    (pts_to0 a p s)
    (pts_to a p s)

let elim_pts_to (#opened: _) (#elt: Type u#1) (a: array elt) (p: P.perm) (s: Seq.seq elt) : SteelGhost unit opened
  (pts_to a p s)
  (fun _ -> R.pts_to a.p.base (mk_carrier (U32.v a.p.base_len) a.p.offset s p))
  (fun _ -> True)
  (fun _ _ _ ->
    valid_perm (U32.v a.p.base_len) a.p.offset (Seq.length s) p /\
    Seq.length s == length a
  )
= change_equal_slprop
    (pts_to a p s)
    (pts_to0 a p s);
  elim_pure _

[@@noextract_to "krml"]
let alloc
  (#elt: Type)
  (x: elt)
  (n: U32.t)
: Steel (array elt)
    emp
    (fun a -> pts_to a P.full_perm (Seq.create (U32.v n) x))
    (fun _ -> True)
    (fun _ a _ -> len a == n)
=
  let c : carrier elt (U32.v n) = mk_carrier (U32.v n) 0 (Seq.create (U32.v n) x) P.full_perm in
  let base : ref (carrier elt (U32.v n)) (pcm elt (U32.v n)) = R.alloc c in
  let p = {
    base_len = n;
    base = base;
    offset = 0;
  }
  in
  let a = {
    p = p;
    length = Ghost.hide (U32.v n);
  }
  in
  change_r_pts_to
    base c
    a.p.base c;
  intro_pts_to a P.full_perm (Seq.create (U32.v n) x);
  return a

let valid_sum_perm
  (len: nat)
  (offset: nat)
  (slice_len: nat)
  (p1 p2: P.perm)
: Tot prop
= let open FStar.Real in
  valid_perm len offset slice_len (P.sum_perm p1 p2)

let mk_carrier_share
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p1 p2: P.perm)
: Lemma
  (requires (valid_sum_perm len offset (Seq.length s) p1 p2))
  (ensures (
    let c1 = mk_carrier len offset s p1 in
    let c2 = mk_carrier len offset s p2 in
      composable c1 c2 /\
      mk_carrier len offset s (p1 `P.sum_perm` p2) `M.equal` (c1 `compose` c2)
  ))
= ()

let share
  (#opened: _)
  (#elt: Type)
  (#x: Seq.seq elt)
  (a: array elt)
  (p p1 p2: P.perm)
: SteelGhost unit opened
    (pts_to a p x)
    (fun _ -> pts_to a p1 x `star` pts_to a p2 x)
    (fun _ -> p == p1 `P.sum_perm` p2)
    (fun _ _ _ -> True)
= elim_pts_to a p x;
  mk_carrier_share (U32.v a.p.base_len) a.p.offset x p1 p2;
  R.split a.p.base _
    (mk_carrier (U32.v a.p.base_len) a.p.offset x p1)
    (mk_carrier (U32.v a.p.base_len) a.p.offset x p2);
  intro_pts_to a p1 x;
  intro_pts_to a p2 x

let mk_carrier_gather
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s1 s2: Seq.seq elt)
  (p1 p2: P.perm)
: Lemma
  (requires (
    let c1 = mk_carrier len offset s1 p1 in
    let c2 = mk_carrier len offset s2 p2 in
    composable c1 c2 /\
    Seq.length s1 == Seq.length s2 /\
    offset + Seq.length s1 <= len
  ))
  (ensures (
    let c1 = mk_carrier len offset s1 p1 in
    let c2 = mk_carrier len offset s2 p2 in
      composable c1 c2 /\
      mk_carrier len offset s1 (p1 `P.sum_perm` p2) == (c1 `compose` c2) /\
      mk_carrier len offset s2 (p1 `P.sum_perm` p2) == (c1 `compose` c2) /\
      s1 == s2
  ))
=
  let c1 = mk_carrier len offset s1 p1 in
  let c2 = mk_carrier len offset s2 p2 in
  assert (composable c1 c2);
  assert (mk_carrier len offset s1 (p1 `P.sum_perm` p2) `M.equal` (c1 `compose` c2));
  assert (mk_carrier len offset s2 (p1 `P.sum_perm` p2) `M.equal` (c1 `compose` c2));
  mk_carrier_inj len offset s1 s2 (p1 `P.sum_perm` p2) (p1 `P.sum_perm` p2)

let mk_carrier_valid_sum_perm
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p1 p2: P.perm)
: Lemma
  (let c1 = mk_carrier len offset s p1 in
   let c2 = mk_carrier len offset s p2 in
   composable c1 c2 <==> valid_sum_perm len offset (Seq.length s) p1 p2)
= let c1 = mk_carrier len offset s p1 in
  let c2 = mk_carrier len offset s p2 in
  if Seq.length s > 0 && offset + Seq.length s <= len
  then
    let open FStar.Real in
    assert (P.composable (M.sel c1 offset) (M.sel c2 offset) <==> valid_perm len offset (Seq.length s) (P.sum_perm p1 p2))
  else ()

let gather
  (#opened: _)
  (#elt: Type)
  (a: array elt)
  (#x1: Seq.seq elt) (p1: P.perm)
  (#x2: Seq.seq elt) (p2: P.perm)
: SteelGhost unit opened
    (pts_to a p1 x1 `star` pts_to a p2 x2)
    (fun _ -> pts_to a (p1 `P.sum_perm` p2) x1)
    (fun _ -> True)
    (fun _ _ _ -> x1 == x2)
= elim_pts_to a p1 x1;
  elim_pts_to a p2 x2;
  R.gather a.p.base
    (mk_carrier (U32.v a.p.base_len) (a.p.offset) x1 p1)
    (mk_carrier (U32.v a.p.base_len) (a.p.offset) x2 p2);
  mk_carrier_gather (U32.v a.p.base_len) (a.p.offset) x1 x2 p1 p2;
  mk_carrier_valid_sum_perm (U32.v a.p.base_len) (a.p.offset) x1 p1 p2;
  intro_pts_to a (p1 `P.sum_perm` p2) x1

[@@noextract_to "krml"]
let index
  (#t: Type) (#p: P.perm)
  (a: array t)
  (#s: Ghost.erased (Seq.seq t))
  (i: U32.t)
: Steel t
    (pts_to a p s)
    (fun _ -> pts_to a p s)
    (fun _ -> U32.v i < length a)
    (fun _ res _ -> U32.v i < Seq.length s /\ res == Seq.index s (U32.v i))
= elim_pts_to a p s;
  let s' = R.read a.p.base _ in
  let res = fst (Some?.v (M.sel s' (a.p.offset + U32.v i))) in
  intro_pts_to a p s;
  return res

let mk_carrier_upd
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (i: nat)
  (v: elt)
  (_: squash (
    offset + Seq.length s <= len /\
    i < Seq.length s
  ))
: Lemma
  (ensures (
    let o = mk_carrier len offset s P.full_perm in
    let o' = mk_carrier len offset (Seq.upd s i v) P.full_perm in
    o' `Map.equal` Map.upd o (offset + i) (Some (v, P.full_perm))
  ))
= ()

[@@noextract_to "krml"]
let upd
  (#t: Type)
  (a: array t)
  (s: Ghost.erased (Seq.seq t))
  (i: U32.t)
  (sq: squash (U32.v i < Seq.length s))
  (v: t)
: SteelT unit
    (pts_to a P.full_perm s)
    (fun res -> pts_to a P.full_perm (Seq.upd s (U32.v i) v))
= elim_pts_to a _ _;
  mk_carrier_upd (U32.v a.p.base_len) (a.p.offset) s (U32.v i) v ();
  R.upd_gen
    a.p.base
    _ _
    (PM.lift_frame_preserving_upd
      _ _
      (P.mk_frame_preserving_upd
        (Seq.index s (U32.v i))
        v
      )
      _ (a.p.offset + U32.v i)
    );
  intro_pts_to a _ _

let adjacent (#elt: Type) (a1 a2: array elt) : Tot prop =
  base a1.p == base a2.p /\
  offset a1.p + a1.length == offset a2.p

inline_for_extraction // this will extract to "let y = a1"
[@@noextract_to "krml"]
let merge (#elt: Type) (a1: array elt) (a2: Ghost.erased (array elt))
: Pure (array elt)
  (requires (adjacent a1 a2))
  (ensures (fun y -> length y == length a1 + length a2))
= {
  p = a1.p;
  length = a1.length + a2.length;
}

let merge_assoc (#elt: Type) (a1 a2 a3: array elt) : Lemma
  (requires (adjacent a1 a2 /\ adjacent a2 a3))
  (ensures (
    adjacent (merge a1 a2) a3 /\ adjacent a1 (merge a2 a3) /\
    merge (merge a1 a2) a3 == merge a1 (merge a2 a3)
  ))
= ()

let merge_into (#elt: Type) (a1 a2 a: array elt) : Tot prop =
  adjacent a1 a2 /\
  merge a1 a2 == a

let mk_carrier_merge
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s1 s2: Seq.seq elt)
  (p: P.perm)
: Lemma
  (requires (
    offset + Seq.length s1 + Seq.length s2 <= len
  ))
  (ensures (
    let c1 = mk_carrier len offset s1 p in
    let c2 = mk_carrier len (offset + Seq.length s1) s2 p in
      composable c1 c2 /\
      mk_carrier len offset (s1 `Seq.append` s2) p `M.equal` (c1 `compose` c2)
  ))
= ()

let ghost_join
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: Seq.seq elt)
  (#p: P.perm)
  (a1 a2: array elt)
: SteelGhost (Ghost.erased (array elt)) opened
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun res -> pts_to res p (x1 `Seq.append` x2))
    (fun _ -> adjacent a1 a2)
    (fun _ res _ -> merge_into a1 a2 res)
= elim_pts_to a1 p x1;
  elim_pts_to a2 p x2;
  mk_carrier_merge (U32.v a1.p.base_len) (a1.p.offset) x1 x2 (p);
  change_r_pts_to
    a2.p.base _
    a1.p.base (mk_carrier (U32.v a1.p.base_len) (a1.p.offset + Seq.length x1) x2 p);
  R.gather a1.p.base
    (mk_carrier (U32.v a1.p.base_len) (a1.p.offset) x1 (p))
    (mk_carrier (U32.v a1.p.base_len) (a1.p.offset + Seq.length x1) x2 (p));
  let res = Ghost.hide (merge a1 a2) in
  change_r_pts_to
    a1.p.base _
    res.p.base (mk_carrier (U32.v res.p.base_len) (res.p.offset) (x1 `Seq.append` x2) (p));
  intro_pts_to res p (Seq.append x1 x2);
  res

inline_for_extraction // this will extract to "let res = a1"
[@@noextract_to "krml"]
let join
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: Ghost.erased (Seq.seq elt))
  (#p: P.perm)
  (a1: array elt)
  (a2: Ghost.erased (array elt))
: SteelAtomicBase (array elt) false opened Unobservable
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun res -> pts_to res p (x1 `Seq.append` x2))
    (fun _ -> adjacent a1 a2)
    (fun _ res _ -> merge_into a1 a2 res)
= let g = ghost_join a1 a2 in
  let res = merge a1 a2 in
  change_equal_slprop
    (pts_to g p (x1 `Seq.append` x2))
    (pts_to res p (x1 `Seq.append` x2));
  return res

let mk_carrier_split
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p: P.perm)
  (i: nat)
: Lemma
  (requires (
    offset + Seq.length s <= len /\
    i <= Seq.length s
  ))
  (ensures (
    let c1 = mk_carrier len offset (Seq.slice s 0 i) p in
    let c2 = mk_carrier len (offset + i) (Seq.slice s i (Seq.length s)) p in
      composable c1 c2 /\
      mk_carrier len offset s p `M.equal` (c1 `compose` c2)
  ))
= ()

inline_for_extraction // this will extract to "let y = a"
[@@noextract_to "krml"]
let split_l (#elt: Type) (a: array elt)
  (i: Ghost.erased U32.t)
: Pure (array elt)
  (requires (U32.v i <= length a))
  (ensures (fun y -> True))
= {
  p = a.p;
  length = U32.v i;
}

// TODO: replace with Ghost, introduce pointer shifting operations in SteelAtomicBase Unobservable
[@@noextract_to "krml"]
let ptr_shift
  (#elt: Type)
  (p: ptr elt)
  (off: U32.t)
: Pure (ptr elt)
  (requires (offset p + U32.v off <= base_len (base p)))
  (ensures (fun p' ->
    base p' == base p /\
    offset p' == offset p + U32.v off
  ))
= {
  base_len = p.base_len;
  base = p.base;
  offset = p.offset + U32.v off;
}

inline_for_extraction
[@@noextract_to "krml"]
let split_r (#elt: Type) (a: array elt)
  (i: U32.t)
: Pure (array elt)
  (requires (U32.v i <= length a))
  (ensures (fun y -> merge_into (split_l a i) y a))
= {
  p = ptr_shift a.p i;
  length = a.length - U32.v i;
}

let ghost_split
  (#opened: _)
  (#elt: Type)
  (#x: Seq.seq elt)
  (#p: P.perm)
  (a: array elt)
  (i: U32.t)
: SteelGhost (squash (U32.v i <= length a /\ U32.v i <= Seq.length x)) opened
    (pts_to a p x)
    (fun res ->
      pts_to (split_l a i) p (Seq.slice x 0 (U32.v i)) `star`
      pts_to (split_r a i) p (Seq.slice x (U32.v i) (Seq.length x)))
    (fun _ -> U32.v i <= length a)
    (fun _ res _ ->
      x == Seq.append (Seq.slice x 0 (U32.v i)) (Seq.slice x (U32.v i) (Seq.length x))
    )
= 
  elim_pts_to a p x;
  mk_carrier_split
    (U32.v a.p.base_len)
    (a.p.offset)
    x
    (p)
    (U32.v i);
  Seq.lemma_split x (U32.v i);
  let xl = Seq.slice x 0 (U32.v i) in
  let xr = Seq.slice x (U32.v i) (Seq.length x) in
  let vl = mk_carrier (U32.v a.p.base_len) (a.p.offset) xl (p) in
  let vr = mk_carrier (U32.v a.p.base_len) (a.p.offset + U32.v i) xr (p) in
  R.split a.p.base _ vl vr;
  change_r_pts_to
    a.p.base vl
    (split_l a i).p.base vl;
  intro_pts_to (split_l a i) #vl p (Seq.slice x 0 (U32.v i));
  change_r_pts_to
    a.p.base vr
    (split_r a i).p.base vr;
  intro_pts_to (split_r a i) #vr p (Seq.slice x (U32.v i) (Seq.length x))
