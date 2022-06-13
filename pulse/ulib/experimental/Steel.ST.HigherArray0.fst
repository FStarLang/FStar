module Steel.ST.HigherArray0

module P = Steel.PCMFrac
module R = Steel.ST.PCMReference
module M = FStar.Map
module PM = Steel.PCMMap

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

[@@erasable]
let base_t (elt: Type u#a) : Tot Type0 = Ghost.erased (base_len: U32.t & ref _ (pcm elt (U32.v base_len)))
let base_len (#elt: Type) (b: base_t elt) : GTot nat = U32.v (dfst b)

[@@noextract_to "krml"]
noeq
type ptr (elt: Type u#a) : Type0 = {
  base_len: Ghost.erased U32.t;
                   // U32.t to prove that A.read, A.write offset computation does not overflow. TODO: replace U32.t with size_t
  base: ref _ (pcm elt (U32.v base_len));
  offset: (offset: nat { offset <= U32.v base_len });
}
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

let valid_perm
  (len: nat)
  (offset: nat)
  (slice_len: nat)
  (p: P.perm) : Tot prop =
  let open FStar.Real in
  ((offset + slice_len <= len /\ slice_len > 0) ==> (p.P.v <=. one))

[@__reduce__]
let pts_to0 (#elt: Type u#1) (a: array elt) (p: P.perm) (s: Seq.seq elt) : Tot vprop =
  R.pts_to (ptr_of a).base (mk_carrier (U32.v (ptr_of a).base_len) (ptr_of a).offset s p) `star`
  pure (
    valid_perm (U32.v (ptr_of a).base_len) (ptr_of a).offset (Seq.length s) p /\
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
: STGhost unit opened
    (R.pts_to p v)
    (fun _ -> R.pts_to p' v')
    (// keep on distinct lines for error messages
      carrier == carrier' /\
      pcm == pcm' /\
      p == p' /\
      v == v')
    (fun _ -> True)
= rewrite
    (R.pts_to p v)
    (R.pts_to p' v')

let intro_pts_to (#opened: _) (#elt: Type u#1) (a: array elt) (#v: _) (p: P.perm) (s: Seq.seq elt) : STGhost unit opened
  (R.pts_to (ptr_of a).base v)
  (fun _ -> pts_to a p s)
  (
    v == mk_carrier (U32.v (ptr_of a).base_len) (ptr_of a).offset s p /\
    valid_perm (U32.v (ptr_of a).base_len) (ptr_of a).offset (Seq.length s) p /\
    Seq.length s == length a
  )
  (fun _ -> True)
= change_r_pts_to (ptr_of a).base v (ptr_of a).base (mk_carrier (U32.v (ptr_of a).base_len) (ptr_of a).offset s p);
  intro_pure _;
  rewrite
    (pts_to0 a p s)
    (pts_to a p s)

let elim_pts_to (#opened: _) (#elt: Type u#1) (a: array elt) (p: P.perm) (s: Seq.seq elt) : STGhost unit opened
  (pts_to a p s)
  (fun _ -> R.pts_to (ptr_of a).base (mk_carrier (U32.v (ptr_of a).base_len) (ptr_of a).offset s p))
  (True)
  (fun _ ->
    valid_perm (U32.v (ptr_of a).base_len) (ptr_of a).offset (Seq.length s) p /\
    Seq.length s == length a
  )
= rewrite
    (pts_to a p s)
    (pts_to0 a p s);
  elim_pure _

let pts_to_length
  a p s
=
  elim_pts_to a p s;
  intro_pts_to a p s

let mk_carrier_joinable
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s1: Seq.seq elt)
  (p1: P.perm)
  (s2: Seq.seq elt)
  (p2: P.perm)
: Lemma
  (requires (
    offset + Seq.length s1 <= len /\
    Seq.length s1 == Seq.length s2 /\
    P.joinable (pcm elt len) (mk_carrier len offset s1 p1) (mk_carrier len offset s2 p2)
  ))
  (ensures (
    s1 `Seq.equal` s2
  ))
=
  let lem
    (i: nat { 0 <= i /\ i < Seq.length s1 })
  : Lemma
    (Seq.index s1 i == Seq.index s2 i)
    [SMTPat (Seq.index s1 i); SMTPat (Seq.index s2 i)]
  = assert (
      forall z . (
        P.compatible (pcm elt len) (mk_carrier len offset s1 p1) z /\
        P.compatible (pcm elt len) (mk_carrier len offset s2 p2) z
      ) ==>
      begin match M.sel z (offset + i) with
      | None -> False
      | Some (v, _) -> v == Seq.index s1 i /\ v == Seq.index s2 i
      end
    )
  in
  ()

let pure_star_interp' (p:slprop u#a) (q:prop) (m:mem)
   : Lemma (interp (p `Steel.Memory.star` Steel.Memory.pure q) m <==>
            interp p m /\ q)
= pure_star_interp p q m;
  emp_unit p

let pts_to_inj
  a p1 s1 p2 s2 m
=
  Classical.forall_intro reveal_pure;
  pure_star_interp'
    (hp_of (R.pts_to (ptr_of a).base (mk_carrier (U32.v (ptr_of a).base_len) (ptr_of a).offset s1 p1)))
    (
      valid_perm (U32.v (ptr_of a).base_len) (ptr_of a).offset (Seq.length s1) p1 /\
      Seq.length s1 == length a
    )
    m;
  pure_star_interp'
    (hp_of (R.pts_to (ptr_of a).base (mk_carrier (U32.v (ptr_of a).base_len) (ptr_of a).offset s2 p2)))
    (
      valid_perm (U32.v (ptr_of a).base_len) (ptr_of a).offset (Seq.length s2) p2 /\
      Seq.length s2 == length a
    )
    m;
  pts_to_join
    (ptr_of a).base
    (mk_carrier (U32.v (ptr_of a).base_len) (ptr_of a).offset s1 p1)
    (mk_carrier (U32.v (ptr_of a).base_len) (ptr_of a).offset s2 p2)
    m;
  mk_carrier_joinable (U32.v (ptr_of a).base_len) (ptr_of a).offset s1 p1 s2 p2

[@@noextract_to "krml"]
let malloc0
  (#elt: Type)
  (x: elt)
  (n: U32.t)
: ST (array elt)
    emp
    (fun a -> pts_to a P.full_perm (Seq.create (U32.v n) x))
    (True)
    (fun a ->
      length a == U32.v n /\
      base_len (base (ptr_of a)) == U32.v n
    )
=
  let c : carrier elt (U32.v n) = mk_carrier (U32.v n) 0 (Seq.create (U32.v n) x) P.full_perm in
  let base : ref (carrier elt (U32.v n)) (pcm elt (U32.v n)) = R.alloc c in
  let p = {
    base_len = n;
    base = base;
    offset = 0;
  }
  in
  let a = (| p, Ghost.hide (U32.v n) |) in
  change_r_pts_to
    base c
    (ptr_of a).base c;
  intro_pts_to a P.full_perm (Seq.create (U32.v n) x);
  return a

let malloc_ptr
  x n
=
  let a = malloc0 x n in
  let (| p, _ |) = a in
  rewrite
    (pts_to _ _ _)
    (pts_to (| p, Ghost.hide (U32.v n) |) _ _);
  return p

[@@noextract_to "krml"]
let free0
  (#elt: Type)
  (#s: Ghost.erased (Seq.seq elt))
  (a: array elt)
: ST unit
    (pts_to a P.full_perm s)
    (fun _ -> emp)
    (
      length a == base_len (base (ptr_of a))
    )
    (fun _ -> True)
= drop (pts_to a _ _)

let free_ptr a =
  free0 _

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
  #_ #_ #x a p p1 p2
= elim_pts_to a p x;
  mk_carrier_share (U32.v (ptr_of a).base_len) (ptr_of a).offset x p1 p2;
  R.split (ptr_of a).base _
    (mk_carrier (U32.v (ptr_of a).base_len) (ptr_of a).offset x p1)
    (mk_carrier (U32.v (ptr_of a).base_len) (ptr_of a).offset x p2);
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
  a #x1 p1 #x2 p2
= elim_pts_to a p1 x1;
  elim_pts_to a p2 x2;
  R.gather (ptr_of a).base
    (mk_carrier (U32.v (ptr_of a).base_len) ((ptr_of a).offset) x1 p1)
    (mk_carrier (U32.v (ptr_of a).base_len) ((ptr_of a).offset) x2 p2);
  mk_carrier_gather (U32.v (ptr_of a).base_len) ((ptr_of a).offset) x1 x2 p1 p2;
  mk_carrier_valid_sum_perm (U32.v (ptr_of a).base_len) ((ptr_of a).offset) x1 p1 p2;
  intro_pts_to a (p1 `P.sum_perm` p2) x1

#push-options "--z3rlimit 16"

[@@noextract_to "krml"]
let index0
  (#t: Type) (#p: P.perm)
  (a: array t)
  (#s: Ghost.erased (Seq.seq t))
  (i: U32.t)
: ST t
    (pts_to a p s)
    (fun _ -> pts_to a p s)
    (U32.v i < length a)
    (fun res -> U32.v i < Seq.length s /\ res == Seq.index s (U32.v i))
= elim_pts_to a p s;
  let s' = R.read (ptr_of a).base _ in
  let res = fst (Some?.v (M.sel s' ((ptr_of a).offset + U32.v i))) in
  intro_pts_to a p s;
  return res

#pop-options

let index_ptr a i =
  index0 _ i

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
let upd0
  (#t: Type)
  (a: array t)
  (#s: Ghost.erased (Seq.seq t))
  (i: U32.t { U32.v i < Seq.length s })
  (v: t)
: STT unit
    (pts_to a P.full_perm s)
    (fun res -> pts_to a P.full_perm (Seq.upd s (U32.v i) v))
= elim_pts_to a _ _;
  mk_carrier_upd (U32.v (ptr_of a).base_len) ((ptr_of a).offset) s (U32.v i) v ();
  R.upd_gen
    (ptr_of a).base
    _ _
    (PM.lift_frame_preserving_upd
      _ _
      (P.mk_frame_preserving_upd
        (Seq.index s (U32.v i))
        v
      )
      _ ((ptr_of a).offset + U32.v i)
    );
  intro_pts_to a _ _

let upd_ptr a i v =
  upd0 _ i v;
  rewrite
    (pts_to _ _ _)
    (pts_to _ _ _)

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
  #_ #_ #x1 #x2 #p a1 a2 h
= elim_pts_to a1 p x1;
  elim_pts_to a2 p x2;
  mk_carrier_merge (U32.v (ptr_of a1).base_len) ((ptr_of a1).offset) x1 x2 (p);
  change_r_pts_to
    (ptr_of a2).base _
    (ptr_of a1).base (mk_carrier (U32.v (ptr_of a1).base_len) ((ptr_of a1).offset + Seq.length x1) x2 p);
  R.gather (ptr_of a1).base
    (mk_carrier (U32.v (ptr_of a1).base_len) ((ptr_of a1).offset) x1 (p))
    (mk_carrier (U32.v (ptr_of a1).base_len) ((ptr_of a1).offset + Seq.length x1) x2 (p));
  change_r_pts_to
    (ptr_of a1).base _
    (ptr_of (merge a1 a2)).base (mk_carrier (U32.v (ptr_of (merge a1 a2)).base_len) ((ptr_of (merge a1 a2)).offset) (x1 `Seq.append` x2) (p));
  intro_pts_to (merge a1 a2) p (Seq.append x1 x2)

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

let ghost_split
  #_ #_ #x #p a i
= 
  elim_pts_to a p x;
  mk_carrier_split
    (U32.v (ptr_of a).base_len)
    ((ptr_of a).offset)
    x
    (p)
    (U32.v i);
  Seq.lemma_split x (U32.v i);
  let xl = Seq.slice x 0 (U32.v i) in
  let xr = Seq.slice x (U32.v i) (Seq.length x) in
  let vl = mk_carrier (U32.v (ptr_of a).base_len) ((ptr_of a).offset) xl (p) in
  let vr = mk_carrier (U32.v (ptr_of a).base_len) ((ptr_of a).offset + U32.v i) xr (p) in
  R.split (ptr_of a).base _ vl vr;
  change_r_pts_to
    (ptr_of a).base vl
    (ptr_of (split_l a i)).base vl;
  intro_pts_to (split_l a i) #vl p (Seq.slice x 0 (U32.v i));
  change_r_pts_to
    (ptr_of a).base vr
    (ptr_of (split_r a i)).base vr;
  intro_pts_to (split_r a i) #vr p (Seq.slice x (U32.v i) (Seq.length x))
