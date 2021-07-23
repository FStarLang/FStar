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

let pts_to' (p: ptr 'a 'b) (pb: pcm 'b) (v: 'b): vprop = vpure (nonnull p pb) `vdep` pts_to_dep p pb v
let pts_to p pb v = pts_to' p pb (Ghost.reveal v)

let pts_to_or_null' (p: ptr 'a 'b) (pb: pcm 'b) (v: option 'b): vprop =
  vpure (v == None <==> p == None) `star`
  (match v with
   | None -> vpure True
   | Some v -> pts_to' p pb v)

let pts_to_or_null p pb v = pts_to_or_null' p pb (Ghost.reveal v)

let nullptr #a #b = None

let vptr r = Some r

let nullptr_vptr_disjoint r = ()

let vptr_injective r r' = ()

let pts_to_nonnull #opened #a #b #pb #v p =
  let _ = gget (pts_to p pb v) in ()

let intro_pts_to #a #b #pb #v r =
  let p = Some r in
  intro_vpure (nonnull p pb);
  intro_vdep (vpure (nonnull p pb)) (r `R.pts_to` v) (pts_to_dep p pb v);
  change_equal_slprop (_ `vdep` _) (pts_to p pb v);
  return p

let elim_pts_to #a #b #pb #v p =
  change_equal_slprop (pts_to p pb v) (vpure (nonnull p pb) `vdep` pts_to_dep p pb v);
  let prf = elim_vdep _ _ in
  elim_vpure _;
  change_equal_slprop (pts_to_dep p pb v prf) _;
  return (Some?.v p)

#push-options "--print_implicits"

(*
let aux' #a #b (pb:pcm b) : unit =
  assert_norm (
    pts_to_or_null #a #b (nullptr #a #b) pb (none #b)  ==
    (if None? #(Steel.C.Ref.ref' a b) (nullptr #a #b)
      then
        Steel.C.Ptr.vpure (Prims.eq2 #(FStar.Ghost.erased (Steel.C.Opt.option b))
	      (Steel.C.Opt.none #b)
              (Steel.C.Opt.none #b))
      else
        (match FStar.Ghost.reveal #(Steel.C.Opt.option b) (Steel.C.Opt.none #b) with
          | FStar.Pervasives.Native.None #_ -> Steel.C.Ptr.vpure Prims.l_False
          | FStar.Pervasives.Native.Some #_ v ->
            Steel.C.Ptr.pts_to #a #b (nullptr #a #b) pb (FStar.Ghost.hide #b v))
        <:
        Steel.Effect.Common.vprop)) // How is this not equal?? TODO
*)

(*
let unfold_pts_to_or_null (p: ptr 'a 'b) (pb: pcm 'b) (v: Ghost.erased (option 'b))
: Lemma
    (pts_to_or_null #'a #'b p pb (none #'b)  ==
     (if None? p then vpure (v == none #'b) else
     (match Ghost.reveal v with
     | None -> vpure False
     | Some v -> pts_to p pb (Ghost.hide v))))
    [SMTPat (pts_to_or_null p pb v)]
= assume // TODO why
    (pts_to_or_null #'a #'b p pb (none #'b)  ==
     (if None? p then vpure (v == none #'b) else
     (match Ghost.reveal v with
     | None -> vpure False
     | Some v -> pts_to p pb (Ghost.hide v))))
*)

let unfold_pts_to_or_null #a #b (pb: pcm b) (p: ptr a b) (v: option b)
: Lemma
    (pts_to_or_null #a #b p pb v  ==
     (vpure (v == None <==> p == None) `star`
     (match v with
      | None -> vpure True
      | Some v -> pts_to p pb v)))
= ()

let intro_pts_to_or_null_nullptr #a #b pb =
  intro_vpure (Ghost.reveal (none #b) == None <==> nullptr #a #b == None);
  intro_vpure True;
  unfold_pts_to_or_null #a #b pb (nullptr #a #b) None; 
  change_equal_slprop _ (pts_to_or_null (nullptr #a #b) pb (none #b))

let intro_pts_to_or_null #a #b #_ #pb #v p =
  let prf_p_nonnull = gget (pts_to p pb v) in
  intro_vpure (Some (Ghost.reveal v) == None <==> p == None);
  unfold_pts_to_or_null pb p (Some (Ghost.reveal v));
  change_equal_slprop
    (vpure (Some (Ghost.reveal v) == None <==> p == None) `star` pts_to' p pb (Ghost.reveal v))
    (pts_to_or_null p pb (some v))
  
val unreachable (#opened:inames) (#p:vprop) (#q:'a -> vprop) (r:'a -> prop)
: SteelGhostF 'a opened p q (requires fun _ -> False) (ensures fun _ x _ -> r x)

let unreachable (#opened:inames) (#p:vprop) (#q:'a -> vprop) (r:'a -> prop)
: SteelGhostF 'a opened p q (requires fun _ -> False) (ensures fun _ x _ -> r x)
= let x: 'a = FStar.IndefiniteDescription.indefinite_description_tot 'a (fun _ -> True) in
  change_slprop_rel p (q x) (fun _ _ -> r x) (fun _ -> ());
  x

let elim_pts_to_or_null_nullptr #a #b #_ #pb #v p =
  let prf: Ghost.erased (
    squash (Ghost.reveal v == None <==> p == None) *
    squash True) = gget (pts_to_or_null p pb v) in
  assert (Ghost.reveal v == None);
  unfold_pts_to_or_null pb p (Ghost.reveal v);
  change_equal_slprop (pts_to_or_null p pb v) 
    (vpure (Ghost.reveal v == None #b <==> p == None #(ref' a b)) `star` vpure True);
  elim_vpure True; elim_vpure _

let elim_pts_to_or_null_nonnull_witness #opened
  (#pb: pcm 'b) (#v: Ghost.erased (option 'b)) (p: ptr 'a 'b)
: SteelGhost (Ghost.erased 'b) opened
    (pts_to_or_null p pb v)
    (fun w -> pts_to_or_null p pb (some w))
    (requires fun _ -> p =!= nullptr)
    (ensures fun _ w _ -> v == some w)
= match Ghost.reveal v with
  | None -> 
    let prf = gget (pts_to_or_null p pb v) in
    let _: squash (Ghost.reveal v == None <==> p == None) = fst prf in
    assert (p == nullptr);
    unreachable (fun w -> v == some w)
  | Some w ->
    let prf = gget (pts_to_or_null p pb v) in
    let _: squash (Ghost.reveal v == None <==> p == None) = fst prf in
    assert (p =!= nullptr);
    change_equal_slprop (pts_to_or_null p pb v) (pts_to_or_null p pb (some w));
    w

#set-options "--ide_id_info_off"

let elim_pts_to_or_null #a #b #_ #pb #v p =
  let w = elim_pts_to_or_null_nonnull_witness p in
  unfold_pts_to_or_null pb p (some w);
  change_equal_slprop (pts_to_or_null p pb (some w))
    (vpure (Ghost.reveal (some w) == None <==> p == None) `star` pts_to' p pb w);
  elim_vpure (Ghost.reveal (some w) == None <==> p == None);
  w
  
let is_null #a #b #pb #v p = return (None? p)

open Steel.C.Connection

let ptr_focused
  (#a:Type) (#b:Type) (#c:Type) (#p: pcm b)
  (r': ptr a c) (r: ptr a b) (#q: pcm c) (l: connection p q)
: prop
= exists (ref_r:ref a p). r == vptr ref_r /\ r' == vptr (ref_focus ref_r l)

let focus #a #b #p r #q l s x =
  let ref_r = elim_pts_to r in
  assert (r == vptr ref_r);
  let ref_r_focused = Steel.C.Ref.focus ref_r l s x in
  let r' = intro_pts_to ref_r_focused in
  assert (r' == vptr (ref_focus ref_r l));
  return r'
  
val elim_pts_to_ghost (#opened:inames)
  (#pb: pcm 'b) (#v: Ghost.erased 'b) (p: ptr 'a 'b)
: SteelGhost (ref 'a pb) opened
    (pts_to p pb v)
    (fun r -> r `R.pts_to` v)
    (requires fun _ -> True)
    (ensures fun _ r _ -> p == vptr r)
let elim_pts_to_ghost #a #b #_ #pb #v p =
  change_equal_slprop (pts_to p pb v) (vpure (nonnull p pb) `vdep` pts_to_dep p pb v);
  let prf = elim_vdep _ _ in
  elim_vpure _;
  let r: ref a pb = Some?.v p in
  change_equal_slprop (pts_to_dep p pb v prf) _;
  r
  
val intro_pts_to_ghost (#opened:inames)
  (#pb: pcm 'b) (#v: Ghost.erased 'b) (r: ref 'a pb)
: SteelGhost (ptr 'a 'b) opened
    (r `R.pts_to` v)
    (fun p -> pts_to p pb v)
    (requires fun _ -> True)
    (ensures fun _ p _ -> p == vptr r)
let intro_pts_to_ghost #a #b #opened #pb #v r =
  let p = Some r in
  intro_vpure (nonnull p pb);
  intro_vdep (vpure (nonnull p pb)) (r `R.pts_to` v) (pts_to_dep p pb v);
  change_equal_slprop (_ `vdep` _) (pts_to p pb v);
  p
    
let unfocus #a #b #c #opened #p #q r r' l x =
  let ref_r' =
    FStar.IndefiniteDescription.indefinite_description_ghost
      (ref a p)
      (fun ref_r -> r' == vptr ref_r /\ r == vptr (ref_focus ref_r l))
  in
  let ref_r = elim_pts_to_ghost r in
  unfocus ref_r ref_r' l x;
  let r'' = intro_pts_to_ghost ref_r' in
  change_equal_slprop (pts_to r'' p _) (pts_to r' p _)

let ptr_opt_write
  (#a:Type) (#b:Type) (#x: Ghost.erased b)
  (p: ptr a (option b)) (y: b)
: SteelT unit
    (pts_to p opt_pcm (some x))
    (fun _ -> pts_to p opt_pcm (some (Ghost.hide y)))
= let r = elim_pts_to p in
  r `opt_write` y;
  let p' = intro_pts_to r in
  change_equal_slprop (pts_to p' opt_pcm _) (pts_to p opt_pcm _)
