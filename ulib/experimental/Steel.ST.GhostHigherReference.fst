module Steel.ST.GhostHigherReference

// needed because I need to know that `Steel.ST.HigherReference.ref a`
// can be turned into `Steel.HigherReference.ref a`
friend Steel.ST.HigherReference

module RST = Steel.ST.HigherReference
module R = Steel.HigherReference

module STC = Steel.ST.Coercions

// FIXME: WHY WHY WHY in `Ghost.reveal (ref a)` is `a` not strictly positive?

[@@erasable]
noeq
type ref' ([@@@strictly_positive] a : Type u#1) : Type0
= | Hide: (reveal: R.ref a) -> ref' a

let ref a = ref' a

let pts_to r p v = RST.pts_to r.reveal p v

let reveal_ref r = r.reveal

let hide_ref r = Hide r

let hide_reveal_ref r = ()

let reveal_pts_to r p x =
  equiv_refl (Steel.ST.HigherReference.pts_to (reveal_ref r) p x)

let pts_to_injective_eq
  #_ #_ #p0 #p1 #v0 #v1 r
= rewrite (pts_to r p0 v0) (RST.pts_to r.reveal p0 v0);
  rewrite (pts_to r p1 v1) (RST.pts_to r.reveal p1 v1);
  RST.pts_to_injective_eq #_ #_ #_ #_ #v0 #v1 r.reveal;
  rewrite (RST.pts_to r.reveal p0 v0) (pts_to r p0 v0);
  rewrite (RST.pts_to r.reveal p1 v0) (pts_to r p1 v0)

let alloc
  #_ #a x
= let gr = STC.coerce_ghost (fun _ -> R.ghost_alloc x) in
  let r = Hide (Ghost.reveal (coerce_eq (R.reveal_ghost_ref a) gr)) in
  weaken (R.ghost_pts_to gr full_perm x) (pts_to r full_perm x) (fun _ ->
    R.reveal_ghost_pts_to_sl gr full_perm x
  );
  r

let write
  #_ #a #v r x
= let gr : R.ghost_ref a = coerce_eq (R.reveal_ghost_ref a) (Ghost.hide r.reveal) in
  weaken (pts_to r full_perm v) (R.ghost_pts_to gr full_perm v) (fun _ ->
    R.reveal_ghost_pts_to_sl gr full_perm v
  );
  STC.coerce_ghost (fun _ -> R.ghost_write gr x);
  weaken (R.ghost_pts_to gr full_perm x) (pts_to r full_perm x) (fun _ ->
    R.reveal_ghost_pts_to_sl gr full_perm x
  )

let free
  #_ #a #v r
= let gr : R.ghost_ref a = coerce_eq (R.reveal_ghost_ref a) (Ghost.hide r.reveal) in
  weaken (pts_to r full_perm v) (R.ghost_pts_to gr full_perm v) (fun _ ->
    R.reveal_ghost_pts_to_sl gr full_perm v
  );
  STC.coerce_ghost (fun _ -> R.ghost_free gr)

let share
  r
= RST.share r.reveal

let gather
  p1 r
= RST.gather p1 r.reveal
