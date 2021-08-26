module Steel.C.Ref
module P = FStar.PCM
module U = Steel.C.Universe
open FStar.FunctionalExtensionality

#push-options "--print_universes"

noeq type ref' (a: Type u#0) (b: Type u#b) : Type u#b = {
  p: pcm a;
  q: pcm b;
  pl: connection p q;
  r: Steel.Memory.ref (U.raise_t u#0 u#1 a) (fstar_pcm_of_pcm (U.raise_pcm p));
}

let pcm_of_ref' r = r.q

let mpts_to (#a: Type u#1) (#p: P.pcm a) (r: Steel.Memory.ref a p) ([@@@smt_fallback] v: a) = Steel.PCMReference.pts_to r v

let raise_p
  (#a: Type u#0)
  (#b: Type u#b)
  (r: ref' a b)
: Tot (pcm (U.raise_t u#0 u#1 a))
= U.raise_pcm r.p

let lower_conn
  (#a: Type u#0)
  (#b: Type u#b)
  (r: ref' a b)
: Tot (connection (raise_p r) r.p)
= connection_of_isomorphism (isomorphism_inverse (U.raise_pcm_isomorphism u#0 u#1 r.p))

let raise_pl
  (#a: Type u#0)
  (#b: Type u#b)
  (r: ref' a b)
: Tot (connection (raise_p r) r.q)
= lower_conn r `connection_compose` r.pl

let pts_to r v =
  r.r `mpts_to` (raise_pl r).conn_small_to_large.morph v

let ref_focus r #q l = {p = r.p; pl = connection_compose r.pl l; r = r.r; q = q}

let ref_focus_id r = connection_compose_id_right r.pl

let ref_focus_comp r l m
= connection_compose_assoc r.pl l m

let mk_id_ref
  (#a: Type0)
  (p: pcm a)
  (r0: Steel.Memory.ref (U.raise_t u#0 u#1 a) (fstar_pcm_of_pcm (U.raise_pcm u#0 u#1 p)))
: Tot (ref a p)
=
  let p' : pcm u#1 _ = U.raise_pcm u#0 u#1 p in
  let fp = fstar_pcm_of_pcm p' in
  let r : ref' a a = { p = p; q = p; pl = connection_id p; r = r0 } in
  r

#push-options "--z3rlimit 16"

let ref_alloc #a p x =
  let x' : U.raise_t u#0 u#1 a = U.raise_val u#0 u#1 x in
  let p' : pcm u#1 _ = U.raise_pcm u#0 u#1 p in
//  let fp : P.pcm u#1 _ = fstar_pcm_of_pcm p' in // FIXME: I can define this local definition, but WHY WHY WHY can't I USE it?
  compatible_refl p' x';
  let r0 : Steel.Memory.ref (U.raise_t u#0 u#1 a) (fstar_pcm_of_pcm (U.raise_pcm u#0 u#1 p)) = Steel.PCMReference.alloc #_ #(fstar_pcm_of_pcm (U.raise_pcm u#0 u#1 p)) x' in
  let r : ref' a a = mk_id_ref p r0 in
  connection_compose_id_right (lower_conn r);
  A.change_equal_slprop (r0 `mpts_to` _) (r `pts_to` x);
  A.return r

#pop-options

let focus r l s x =
  let r' = ref_focus r l in
  connection_compose_assoc (lower_conn r) r.pl l;
  A.change_equal_slprop
    (r `pts_to` s)
    (r' `pts_to` x);
  A.return r'

let unfocus r r' l x =
  connection_compose_assoc (lower_conn r') r'.pl l;
  A.change_equal_slprop
    (r `pts_to` x)
    (r' `pts_to` l.conn_small_to_large.morph x)

let split r xy x y =
  let c = raise_pl r in
  let xy2 = Ghost.hide (c.conn_small_to_large.morph xy) in
  let x2 = Ghost.hide (c.conn_small_to_large.morph x) in
  let y2 = Ghost.hide (c.conn_small_to_large.morph y) in
  assert (composable (raise_p r) x2 y2);
  A.change_equal_slprop
    (r `pts_to` xy)
    (r.r `mpts_to` xy2);
  Steel.PCMReference.split r.r
    xy2
    x2
    y2;
  A.change_equal_slprop
    (r.r `mpts_to` x2)
    (r `pts_to` x);
  A.change_equal_slprop
    (r.r `mpts_to` y2)
    (r `pts_to` y)

let mgather
  (#a:Type) (#p:P.pcm a)
  (r:Steel.Memory.ref a p) (v0:Ghost.erased a) (v1:Ghost.erased a)
: SteelT (_:unit{P.composable p v0 v1})
    (mpts_to r v0 `star` mpts_to r v1)
    (fun _ -> mpts_to r (P.op p v0 v1))
= Steel.PCMReference.gather r v0 v1

let gather #a #b #p r x y =
  let c = raise_pl r in
  let x2 = Ghost.hide (c.conn_small_to_large.morph x) in
  let y2 = Ghost.hide (c.conn_small_to_large.morph y) in
  A.change_equal_slprop
    (r `pts_to` x)
    (r.r `mpts_to` x2);
  A.change_equal_slprop
    (r `pts_to` y)
    (r.r `mpts_to` y2);
  mgather r.r
    x2
    y2;
  assert (composable (raise_p r) x2 y2);
  assert (
    let x' = c.conn_large_to_small.morph x2 in
    let y' = c.conn_large_to_small.morph y2 in
    composable p x' y' /\
    Ghost.reveal x == x' /\ Ghost.reveal y == y'
  );
  A.change_equal_slprop _ (r `pts_to` op p x y)

let ref_read (#p: pcm 'b) (#x: Ghost.erased 'b) (r: ref 'a p)
: Steel 'b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> True)
    (ensures fun _ x' _ -> compatible p x x')
= let w = Ghost.hide ((raise_pl r).conn_small_to_large.morph x) in
  A.change_equal_slprop (r `pts_to` x) (r.r `mpts_to` w);
  let w' = Steel.PCMReference.read r.r w in
  A.change_equal_slprop (r.r `mpts_to` w) (r `pts_to` x);
  let x' = (raise_pl r).conn_large_to_small.morph w' in
  compatible_morphism (raise_pl r).conn_large_to_small w w';
  A.return x'

let ref_upd_act (r: ref 'a 'p) (x: Ghost.erased 'b { ~ (Ghost.reveal x == one 'p) }) (y: Ghost.erased 'b) (f: frame_preserving_upd 'p x y)
: Tot (M.action_except unit Set.empty (hp_of (r `pts_to` x)) (fun _ -> hp_of (r `pts_to` y)))
= let c = raise_pl r in
  let x' = Ghost.hide (c.conn_small_to_large.morph x) in
  let y' = Ghost.hide (c.conn_small_to_large.morph y) in
  M.upd_gen Set.empty r.r x' y' (fstar_fpu_of_fpu (raise_p r) x' y' (c.conn_lift_frame_preserving_upd (|x, y, restricted_frame_preserving_upd_intro f|) ))

let as_action (#p:vprop)
              (#q:vprop)
              (f:M.action_except unit Set.empty (hp_of p) (fun _ -> hp_of q))
: SteelT unit p (fun x -> q)
= A.change_slprop_rel p (to_vprop (hp_of p)) (fun _ _ -> True) (fun m -> ());
  let x = Steel.Effect.as_action f in
  A.change_slprop_rel (to_vprop (hp_of q)) q (fun _ _ -> True) (fun m -> ());
  A.return x

let ref_upd r x y f = as_action (ref_upd_act r x y f)

let base_fpu p x y =
  fun _ ->
  compatible_refl p y;
  y

let pts_to_view_explicit_witinv
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type u#c)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: Lemma
  (M.is_witness_invariant (pts_to_view_explicit r vw))
= let aux (x y : Ghost.erased c) (m:M.mem)
  : Lemma
    (requires (M.interp (pts_to_view_explicit r vw x) m /\ M.interp (pts_to_view_explicit r vw y) m))
    (ensures  (x == y))
  =
    let c = raise_pl r in
    let x_ = vw.to_carrier x in
    let y_ = vw.to_carrier y in
    let x' = c.conn_small_to_large.morph x_ in
    let y' = c.conn_small_to_large.morph y_ in
    M.pts_to_join r.r x' y' m;
    let z' = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun z' -> compatible (raise_p r) x' z' /\ compatible (raise_p r) y' z') in
    let frame_x' = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun frame_x' -> composable (raise_p r) x' frame_x' /\ op (raise_p r) frame_x' x' == z') in
    let frame_y' = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun frame_y' -> composable (raise_p r) y' frame_y' /\ op (raise_p r) frame_y' y' == z') in
    let frame_x_ = c.conn_large_to_small.morph frame_x' in
    let frame_y_ = c.conn_large_to_small.morph frame_y' in
    op_comm (raise_p r) x' frame_x';
    c.conn_large_to_small.morph_compose x' frame_x';
    vw.to_view_frame x (c.conn_large_to_small.morph frame_x');
    op_comm (raise_p r) y' frame_y';
    c.conn_large_to_small.morph_compose y' frame_y';
    vw.to_view_frame y (c.conn_large_to_small.morph frame_y');
    ()
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (aux x y))
