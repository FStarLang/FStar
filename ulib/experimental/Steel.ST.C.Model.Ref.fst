module Steel.ST.C.Model.Ref
module P = FStar.PCM
module U = Steel.C.Model.Universe
open FStar.FunctionalExtensionality

friend Steel.C.Model.Ref.Base

let mk_id_ref
  (#a: Type0)
  (p: pcm a)
  (r0: Steel.Memory.ref (U.raise_t u#0 u#1 a) (fstar_pcm_of_pcm (U.raise_pcm u#0 u#1 p)))
: Tot (ref a p)
=
  let p' : pcm u#1 _ = U.raise_pcm u#0 u#1 p in
  let fp = fstar_pcm_of_pcm p' in
  NonNull ({ p = p; q = p; pl = connection_id p; r = r0 })

#push-options "--z3rlimit 16"

let ref_alloc #a p x =
  let x' : U.raise_t u#0 u#1 a = U.raise_val u#0 u#1 x in
  let p' : pcm u#1 _ = U.raise_pcm u#0 u#1 p in
//  let fp : P.pcm u#1 _ = fstar_pcm_of_pcm p' in // FIXME: I can define this local definition, but WHY WHY WHY can't I USE it?
  compatible_refl p' x';
  let r0 : Steel.Memory.ref (U.raise_t u#0 u#1 a) (fstar_pcm_of_pcm (U.raise_pcm u#0 u#1 p)) = Steel.ST.PCMReference.alloc #_ #(fstar_pcm_of_pcm (U.raise_pcm u#0 u#1 p)) x' in
  let r : ref a p = mk_id_ref p r0 in
  connection_compose_id_right (lower_conn r);
  rewrite (r0 `mpts_to` _) (r `pts_to` x);
  return r

let ref_free #a #b #p #x r =
  // TODO: use Steel.PCMReference.free, but we are blocked by (p.refine (one p)), which we explicitly excluded in Steel.C.Model.PCM
  drop (pts_to _ _)

#pop-options

let gfocus r l s x =
  connection_compose_assoc (lower_conn r) (NonNull?.v r).pl l;
  rewrite
    (r `pts_to` s)
    (ref_focus r l `pts_to` x)

let focus r l s x =
  let r' = t_ref_focus r l in
  gfocus r l s x;
  rewrite
    (ref_focus r l `pts_to` x)
    (r' `pts_to` x);
  return r'

let unfocus r r' l x =
  connection_compose_assoc (lower_conn r') (NonNull?.v r').pl l;
  rewrite
    (r `pts_to` x)
    (r' `pts_to` l.conn_small_to_large.morph x)

let split r xy x y =
  let c = raise_pl r in
  let xy2 = Ghost.hide (c.conn_small_to_large.morph xy) in
  let x2 = Ghost.hide (c.conn_small_to_large.morph x) in
  let y2 = Ghost.hide (c.conn_small_to_large.morph y) in
  assert (composable (raise_p r) x2 y2);
  rewrite
    (r `pts_to` xy)
    ((NonNull?.v r).r `mpts_to` xy2);
  Steel.ST.PCMReference.split (NonNull?.v r).r
    xy2
    x2
    y2;
  rewrite
    ((NonNull?.v r).r `mpts_to` x2)
    (r `pts_to` x);
  rewrite
    ((NonNull?.v r).r `mpts_to` y2)
    (r `pts_to` y)

let mgather
  (#inames: _) (#a:Type) (#p:P.pcm a)
  (r:Steel.Memory.ref a p) (v0:Ghost.erased a) (v1:Ghost.erased a)
: STGhostT (_:unit{P.composable p v0 v1}) inames
    (mpts_to r v0 `star` mpts_to r v1)
    (fun _ -> mpts_to r (P.op p v0 v1))
= Steel.ST.PCMReference.gather r v0 v1

let gather #inames #a #b #p r x y =
  let c = raise_pl r in
  let x2 = Ghost.hide (c.conn_small_to_large.morph x) in
  let y2 = Ghost.hide (c.conn_small_to_large.morph y) in
  rewrite
    (r `pts_to` x)
    ((NonNull?.v r).r `mpts_to` x2);
  rewrite
    (r `pts_to` y)
    ((NonNull?.v r).r `mpts_to` y2);
  let _ = mgather (NonNull?.v r).r
    x2
    y2
  in
  assert (composable (raise_p r) x2 y2);
  assert (
    let x' = c.conn_large_to_small.morph x2 in
    let y' = c.conn_large_to_small.morph y2 in
    composable p x' y' /\
    Ghost.reveal x == x' /\ Ghost.reveal y == y'
  );
  rewrite _ (r `pts_to` op p x y)

let ref_read
  #_ #_ #p #x r
= let w = Ghost.hide ((raise_pl r).conn_small_to_large.morph x) in
  rewrite (r `pts_to` x) ((NonNull?.v r).r `mpts_to` w);
  let w' = Steel.ST.PCMReference.read (NonNull?.v r).r w in
  rewrite ((NonNull?.v r).r `mpts_to` w) (r `pts_to` x);
  let x' = (raise_pl r).conn_large_to_small.morph w' in
  compatible_morphism (raise_pl r).conn_large_to_small w w';
  return x'

let ref_upd_act (r: ref 'a 'p) (x: Ghost.erased 'b { ~ (Ghost.reveal x == one 'p) }) (y: Ghost.erased 'b) (f: frame_preserving_upd 'p x y)
: Tot (M.action_except unit Set.empty (hp_of (r `pts_to` x)) (fun _ -> hp_of (r `pts_to` y)))
= let c = raise_pl r in
  let x' = Ghost.hide (c.conn_small_to_large.morph x) in
  let y' = Ghost.hide (c.conn_small_to_large.morph y) in
  M.upd_gen Set.empty (NonNull?.v r).r x' y' (fstar_fpu_of_fpu (raise_p r) x' y' (mk_restricted_frame_preserving_upd (c.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = restricted_frame_preserving_upd_intro f; }) )))

let as_action (#p:vprop)
              (#q:vprop)
              (f:M.action_except unit Set.empty (hp_of p) (fun _ -> hp_of q))
: STT unit p (fun x -> q)
= weaken p (to_vprop (hp_of p)) (fun m -> ());
  let x = Steel.ST.Coercions.coerce_steel (fun _ -> Steel.Effect.as_action f) in
  weaken (to_vprop (hp_of q)) q (fun m -> ());
  return x

let ref_upd r x y f = as_action (ref_upd_act r x y f)
