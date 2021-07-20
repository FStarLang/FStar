module Steel.C.Ptr

module P = FStar.PCM
module R = Steel.C.Ref
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Ref
open Steel.Effect

let vpure_sel'
  (p: prop)
: Tot (selector' (squash p) (Steel.Memory.pure p))
= fun (m: Steel.Memory.hmem (Steel.Memory.pure p)) -> pure_interp p m

let vpure_sel
  (p: prop)
: Tot (selector (squash p) (Steel.Memory.pure p))
= vpure_sel' p

[@@ __steel_reduce__]
let vpure'
  (p: prop)
: GTot vprop'
= {
  hp = Steel.Memory.pure p;
  t = squash p;
  sel = vpure_sel p;
}

[@@ __steel_reduce__]
let vpure (p: prop) : Tot vprop = VUnit (vpure' p)

let intro_vpure
  (#opened: _)
  (p: prop)
: SteelGhost unit opened
    emp
    (fun _ -> vpure p)
    (fun _ -> p)
    (fun _ _ h' -> p)
=
  change_slprop_rel
    emp
    (vpure p)
    (fun _ _ -> p)
    (fun m -> pure_interp p m)

let elim_vpure
  (#opened: _)
  (p: prop)
: SteelGhost unit opened
    (vpure p)
    (fun _ -> emp)
    (fun _ -> True)
    (fun _ _ _ -> p)
=
  change_slprop_rel
    (vpure p)
    emp
    (fun _ _ -> p)
    (fun m -> pure_interp p m; reveal_emp (); intro_emp m)

// ----------------------------------------

let ptr a b = option (ref' a b)

let nonnull (p: ptr 'a 'b) (pb: pcm 'b): prop = Some? p /\ pcm_of_ref' (Some?.v p) == pb

let pts_to_dep (p: ptr 'a 'b) (pb: pcm 'b) (v: Ghost.erased 'b) (prf: squash (nonnull p pb))
= let r: ref 'a pb = Some?.v p in r `pts_to` v

let pts_to p pb v = vpure (nonnull p pb) `vdep` pts_to_dep p pb v

let pts_to_or_null p pb v = if None? p then vpure True else pts_to p pb v

let nullptr #a #b = None

let vptr r = Some r

let intro_pts_to #a #b #pb #v r =
  let p = Some r in
  intro_vpure (nonnull p pb);
  intro_vdep (vpure (nonnull p pb)) (r `R.pts_to` v) (pts_to_dep p pb v);
  change_equal_slprop (_ `vdep` _) (pts_to p pb v);
  return p

let elim_pts_to #a #b #opened #pb #v r p =
  change_equal_slprop (pts_to p pb v) (vpure (nonnull p pb) `vdep` pts_to_dep p pb v);
  let prf = elim_vdep _ _ in
  elim_vpure _;
  change_equal_slprop (pts_to_dep p pb v prf) _

let intro_pts_to_or_null_nullptr #a pb v = intro_vpure True

let intro_pts_to_or_null #a #b #pb #v p =
  change_equal_slprop (pts_to p pb v) (pts_to_or_null p pb v);
  return p

let elim_pts_to_or_null #a #b #pb #v p =
  change_equal_slprop (pts_to_or_null p pb v) (pts_to p pb v);
  return p

let is_null #a #b #pb #v p = return (None? p)
