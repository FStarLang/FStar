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

(*
/// Gather permissions on reference [r]
let derive_composable (#o:inames)
           (#a:Type u#1)
           (#p:P.pcm a)
           (r:ref a p)
           (v0:a)
           (v1:a)
  : SteelGhost unit o
           (R.pts_to r v0 `star` R.pts_to r v1)
           (fun _ -> R.pts_to r v0 `star` R.pts_to r v1)
           (fun _ -> True)
           (fun _ _ _ -> FStar.PCM.composable p v0 v1)
= R.gather r v0 v1;
  R.split r _ v0 v1
*)

[@@noextract_to "krml"]
let index_t (len: nat) : Tot eqtype = (i: nat { i < len })

[@@noextract_to "krml"]
let carrier (elt: Type u#a) (len: nat) : Tot Type =
  PM.map (index_t len) (P.fractional elt)

[@@noextract_to "krml"]
let pcm (elt: Type u#a) (len: nat) : Tot (P.pcm (carrier elt len)) =
  PM.pointwise (index_t len) (P.pcm_frac #elt)

[@@noextract_to "krml"]
let one (#elt: Type) (#len: nat) = (pcm elt len).P.p.P.one
let composable (#elt: Type) (#len: nat) = (pcm elt len).P.p.P.composable
[@@noextract_to "krml"]
let compose (#elt: Type) (#len: nat) = (pcm elt len).P.p.P.op

[@@noextract_to "krml"]
let mk_carrier
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p: P.perm)
: Tot (carrier elt len)
= let f (i: index_t len) : Tot (P.fractional elt) =
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
  base_len: U32.t; // cannot be erased because I need to know the size of the carrier elements.
                   // U32.t to prove that A.read, A.write offset computation does not overflow. TODO: replace U32.t with size_t
  base: ref _ (pcm elt (U32.v base_len));
  offset: (offset: nat { offset <= U32.v base_len });
}

inline_for_extraction // Karamel should extract this to ptr, erasing the length and prf fields
[@@noextract_to "krml"]
noeq
type array (elt: Type) = {
  p: ptr elt;
  length: Ghost.erased nat;
  prf: squash (p.offset + length <= U32.v p.base_len);
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
  (v v': carrier)
: SteelGhost unit opened
    (R.pts_to p v)
    (fun _ -> R.pts_to p v')
    (fun _ -> v == v')
    (fun _ _ _ -> True)
= change_equal_slprop
    (R.pts_to p v)
    (R.pts_to p v')

let intro_pts_to (#opened: _) (#elt: Type u#1) (a: array elt) (#v: _) (p: P.perm) (s: Seq.seq elt) : SteelGhost unit opened
  (R.pts_to a.p.base v)
  (fun _ -> pts_to a p s)
  (fun _ ->
    v == mk_carrier (U32.v a.p.base_len) a.p.offset s p /\
    valid_perm (U32.v a.p.base_len) a.p.offset (Seq.length s) p /\
    Seq.length s == length a
  )
  (fun _ _ _ -> True)
= change_r_pts_to a.p.base v (mk_carrier (U32.v a.p.base_len) a.p.offset s p);
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

(*
let elim_pts_to_get_base (#opened: _) (#elt: Type u#1) (a: array elt) (p: P.perm) (s: Seq.seq elt) : Steel (ref (carrier_of a) (pcm 
Ghost.erased (carrier elt (U32.v a.p.base_len))) opened
  (pts_to a p s)
  (fun v -> R.pts_to a.p.base v)
  (fun _ -> True)
  (fun _ v _ ->
    Ghost.reveal v == mk_carrier (U32.v a.p.base_len) a.p.offset s p /\
    valid_perm (U32.v a.p.base_len) a.p.offset (Seq.length s) p /\
    Seq.length s == length a
  )
= let res = Ghost.hide (mk_carrier (U32.v a.p.base_len) a.p.offset s p) in
  elim_pts_to a p s;
  change_r_pts_to a.p.base _ res;
  res
*)

let change_equal_slprop_by_trefl (#opened:inames) (p q: vprop)
  : SteelGhost unit opened p (fun _ -> q) (fun _ -> FStar.Tactics.with_tactic FStar.Tactics.trefl (p == q)) (fun h0 _ h1 -> p == q /\ h1 q == h0 p)
= change_equal_slprop p q

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
    prf = ();
  }
  in
  change_equal_slprop_by_trefl
    (R.pts_to base c)
    (R.pts_to a.p.base c);
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

let mk_carrier_index
  (#elt: Type)
  (len: nat)
  (offset1: nat)
  (s1: Seq.seq elt)
  (p1: P.perm)
  (i1: nat)
  (s1': carrier elt len)
  (_: squash (
    offset1 + Seq.length s1 <= len /\
    i1 < Seq.length s1 /\
    P.compatible (pcm elt len) (mk_carrier len offset1 s1 p1) s1'
  ))
: Lemma
  (ensures (
    match M.sel s1' (offset1 + i1) with
    | None -> False
    | Some (v, _) -> v == Seq.index s1 i1
  ))
= ()

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
  let s' = R.read a.p.base _ in // here pcm needs a.p.base_len non-erased
  mk_carrier_index (U32.v a.p.base_len)
    (a.p.offset) s p (U32.v i) s' ();
  let res = fst (Some?.v (M.sel s' (a.p.offset + U32.v i))) in
  intro_pts_to a p s;
  return res

let mk_carrier_index_simple
  (#elt: Type)
  (len: nat)
  (offset1: nat)
  (s1: Seq.seq elt)
  (p1: P.perm)
  (i1: nat)
  (_: squash (
    offset1 + Seq.length s1 <= len /\
    i1 < Seq.length s1
  ))
: Lemma
  (ensures (
    let s1' = mk_carrier len offset1 s1 p1 in
    match M.sel s1' (offset1 + i1) with
    | None -> False
    | Some (v, _) -> v == Seq.index s1 i1
  ))
= ()

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
  mk_carrier_index_simple (U32.v a.p.base_len) a.p.offset s P.full_perm (U32.v i) ();
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

(*
let adjacent (#elt: Type) (a1 a2: array elt) : Tot prop =
  a1.p.base_len == a2.p.base_len /\
  a1.p.base == a2.p.base /\
  a1.p.offset + a1.length == a2.p.offset



inline_for_extraction
[@@noextract_to "krml"]
let merge (#elt: Type) (a1 a2: array_slice elt)
: Pure (array_slice elt)
  (requires (adjacent a1 a2))
  (ensures (fun y -> length y == length a1 + length a2))
= {
  base = a1.base;
  base_gr = a1.base_gr;
  base_inv = a1.base_inv;
  base_len = a1.base_len;
  offset = a1.offset;
  length = U32.add a1.length a2.length;
  prf = ();
}

let merge_assoc (#elt: Type) (a1 a2 a3: array_slice elt) : Lemma
  (requires (adjacent a1 a2 /\ adjacent a2 a3))
  (ensures (
    adjacent (merge a1 a2) a3 /\ adjacent a1 (merge a2 a3) /\
    merge (merge a1 a2) a3 == merge a1 (merge a2 a3)
  ))
= ()

let merge_into (#elt: Type) (a1 a2 a: array_slice elt) : Tot prop =
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
  (#p: perm)
  (a1 a2: array_slice elt)
: STGhost (Ghost.erased (array_slice elt)) opened
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun res -> pts_to res p (x1 `Seq.append` x2))
    (adjacent a1 a2)
    (fun res -> merge_into a1 a2 res)
= rewrite
    (pts_to a1 p x1)
    (pts_to0 a1 p x1);
  rewrite
    (pts_to a2 p x2)
    (pts_to0 a2 p x2);
  let _ = gen_elim () in
  mk_carrier_merge (A.length a1.base) (U32.v a1.offset) x1 x2 (P.half_perm p);
  rewrite
    (R.pts_to a2.base_gr (mk_carrier (A.length a2.base) (U32.v a2.offset) x2 (P.half_perm p)))
    (R.pts_to a1.base_gr (mk_carrier (A.length a1.base) (U32.v a1.offset + Seq.length x1) x2 (P.half_perm p)));
  R.gather a1.base_gr
    (mk_carrier (A.length a1.base) (U32.v a1.offset) x1 (P.half_perm p))
    (mk_carrier (A.length a1.base) (U32.v a1.offset + Seq.length x1) x2 (P.half_perm p));
  let res = Ghost.hide (merge a1 a2) in
  rewrite
    (R.pts_to a1.base_gr _)
    (R.pts_to res.base_gr (mk_carrier (A.length res.base) (U32.v res.offset) (x1 `Seq.append` x2) (P.half_perm p)));
  rewrite
    (pts_to0 res p (Seq.append x1 x2))
    (pts_to res p (Seq.append x1 x2));
  res

inline_for_extraction
[@@noextract_to "krml"]
let join
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: Ghost.erased (Seq.seq elt))
  (#p: perm)
  (a1 a2: array_slice elt)
: STAtomicBase (array_slice elt) false opened Unobservable
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun res -> pts_to res p (x1 `Seq.append` x2))
    (adjacent a1 a2)
    (fun res -> merge_into a1 a2 res)
= let g = ghost_join a1 a2 in
  let res = merge a1 a2 in
  rewrite
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

inline_for_extraction
[@@noextract_to "krml"]
let tsplit (#elt: Type) (a: array_slice elt)
  (i: U32.t)
: Pure (array_slice elt & array_slice elt)
  (requires (U32.v i <= length a))
  (ensures (fun y -> merge_into (fst y) (snd y) a))
= (
    {
      base = a.base;
      base_gr = a.base_gr;
      base_inv = a.base_inv;
      base_len = a.base_len;
      offset = a.offset;
      length = i;
      prf = ();
    }, {
      base = a.base;
      base_gr = a.base_gr;
      base_inv = a.base_inv;
      base_len = a.base_len;
      offset = a.offset `U32.add` i;
      length = a.length `U32.sub` i;
      prf = ();
    }
  )
    
#set-options "--ide_id_info_off"

let ghost_split
  (#opened: _)
  (#elt: Type)
  (#x: Seq.seq elt)
  (#p: perm)
  (a: array_slice elt)
  (i: U32.t)
: STGhost (Ghost.erased (array_slice elt & array_slice elt)) opened
    (pts_to a p x)
    (fun res -> exists_ (fun x1 -> exists_ (fun x2 ->
      pts_to (fst res) p x1 `star`
      pts_to (snd res) p x2 `star`
      pure (
        U32.v i <= length a /\
        U32.v i <= Seq.length x /\
        x1 == Seq.slice x 0 (U32.v i) /\
        x2 == Seq.slice x (U32.v i) (Seq.length x) /\
        x == x1 `Seq.append` x2 /\
        Ghost.reveal res == tsplit a i
    ))))
    (U32.v i <= length a)
    (fun _ -> True)
= rewrite
    (pts_to a p x)
    (pts_to0 a p x);
  let _ = gen_elim () in
  mk_carrier_split
    (U32.v a.p.base_len)
    (a.p.offset)
    x
    (P.half_perm p)
    (U32.v i);
  Seq.lemma_split x (U32.v i);
  let xl = Seq.slice x 0 (U32.v i) in
  let xr = Seq.slice x (U32.v i) (Seq.length x) in
  let vl = mk_carrier (U32.v a.p.base_len) (a.p.offset) xl (P.half_perm p) in
  let vr = mk_carrier (U32.v a.p.base_len) (a.p.offset + U32.v i) xr (P.half_perm p) in
  R.share a.base_gr _ vl vr;
  let res = Ghost.hide (tsplit a i) in
  rewrite
    (R.pts_to a.base_gr vl)
    (R.pts_to (fst res).base_gr (mk_carrier (A.length (fst res).base) (U32.v (fst res).offset) xl (P.half_perm p)));
  rewrite
    (pts_to0 (fst res) p xl)
    (pts_to (fst res) p xl);
  rewrite
    (R.pts_to a.base_gr vr)
    (R.pts_to (snd res).base_gr (mk_carrier (A.length (snd res).base) (U32.v (snd res).offset) xr (P.half_perm p)));
  rewrite
    (pts_to0 (snd res) p xr)
    (pts_to (snd res) p xr);
  res

inline_for_extraction
[@@noextract_to "krml"]
let split
  (#opened: _)
  (#elt: Type)
  (#x: Ghost.erased (Seq.seq elt))
  (#p: perm)
  (a: array_slice elt)
  (i: U32.t)
: STAtomicBase (array_slice elt & array_slice elt) false opened Unobservable
    (pts_to a p x)
    (fun res -> exists_ (fun x1 -> exists_ (fun x2 ->
      pts_to (fst res) p x1 `star`
      pts_to (snd res) p x2 `star`
      pure (
        U32.v i <= length a /\
        U32.v i <= Seq.length x /\
        x1 == Seq.slice x 0 (U32.v i) /\
        x2 == Seq.slice x (U32.v i) (Seq.length x) /\
        Ghost.reveal x == x1 `Seq.append` x2 /\
        res == tsplit a i
    ))))
    (U32.v i <= length a)
    (fun _ -> True)
= let g = ghost_split a i in
  let _ = gen_elim () in
  let res = tsplit a i in
  let x1 = vpattern_erased (fun x1 -> pts_to (fst g) p x1) in
  rewrite
    (pts_to (fst g) p _)
    (pts_to (fst res) p x1);
  let x2 = vpattern_erased (fun x2 -> pts_to (snd g) p x2) in
  rewrite
    (pts_to (snd g) p _)
    (pts_to (snd res) p x2);
  return res
