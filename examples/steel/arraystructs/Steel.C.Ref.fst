module Steel.C.Ref
module P = FStar.PCM
open FStar.FunctionalExtensionality

#push-options "--print_universes"

noeq type ref (a: Type u#1) (#b: Type u#b) (q: pcm b): Type u#(max 1 b) = {
  p: pcm a;
  pl: connection p q;
  r: Steel.Memory.ref a p;
}

let mpts_to (#p: pcm 'a) (r: Steel.Memory.ref 'a p) = Steel.PCMReference.pts_to r

let pts_to r v =
  r.r `mpts_to` r.pl.conn_small_to_large.morph v
  
let ref_focus r l = {p = r.p; pl = connection_compose r.pl l; r = r.r}

let ref_focus_id r = connection_compose_id_right r.pl

let ref_focus_comp r l m
= connection_eq
    ((r.pl `connection_compose` l) `connection_compose` m)
    (r.pl `connection_compose` (l `connection_compose` m))

let focus r l s x =
  let r' = ref_focus r l in
  A.change_slprop_rel  
    (r `pts_to` s)
    (r' `pts_to` x)
    (fun _ _ -> True)
    (fun m -> ());
  A.return r'

let unfocus r r' l x =
  A.change_slprop_rel  
    (r `pts_to` x)
    (r' `pts_to` l.conn_small_to_large.morph x)
    (fun _ _ -> True)
    (fun m -> ())

let split r xy x y =
  A.change_equal_slprop
    (r `pts_to` xy)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (r.pl.conn_small_to_large.morph xy)));
  Steel.PCMReference.split r.r
    (r.pl.conn_small_to_large.morph xy)
    (r.pl.conn_small_to_large.morph x)
    (r.pl.conn_small_to_large.morph y);
  A.change_equal_slprop
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (r.pl.conn_small_to_large.morph x)))
    (r `pts_to` x);
  A.change_equal_slprop
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (r.pl.conn_small_to_large.morph y)))
    (r `pts_to` y)

let mgather
  (#a:Type) (#p:pcm a)
  (r:Steel.Memory.ref a p) (v0:Ghost.erased a) (v1:Ghost.erased a)
: SteelT (_:unit{composable p v0 v1})
    (mpts_to r v0 `star` mpts_to r v1)
    (fun _ -> mpts_to r (op p v0 v1))
= Steel.PCMReference.gather r v0 v1

let gather #a #b #p r x y =
  A.change_equal_slprop
    (r `pts_to` x)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (r.pl.conn_small_to_large.morph x)));
  A.change_equal_slprop
    (r `pts_to` y)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (r.pl.conn_small_to_large.morph y)));
  mgather r.r
    (r.pl.conn_small_to_large.morph x)
    (r.pl.conn_small_to_large.morph y);
  assert (
    let x1 = r.pl.conn_small_to_large.morph x in
    let y1 = r.pl.conn_small_to_large.morph y in
    let x2 = r.pl.conn_large_to_small.morph x1 in
    let y2 = r.pl.conn_large_to_small.morph y1 in
    Ghost.reveal x == x2 /\ Ghost.reveal y == y2
  );
  A.change_equal_slprop _ (r `pts_to` op p x y)

let ref_read (#p: pcm 'b) (#x: Ghost.erased 'b) (r: ref 'a p)
: Steel 'b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> True)
    (ensures fun _ x' _ -> compatible p x x')
= let w = Ghost.hide (r.pl.conn_small_to_large.morph x) in
  A.change_equal_slprop (r `pts_to` x) (r.r `mpts_to` w);
  let w' = Steel.PCMReference.read r.r w in
  A.change_equal_slprop (r.r `mpts_to` w) (r `pts_to` x);
  let x' = r.pl.conn_large_to_small.morph w' in
  assert (forall frame . (composable r.p w frame /\ op r.p frame w == w') ==> (
    let sw = r.pl.conn_large_to_small.morph w in
    let sw' = r.pl.conn_large_to_small.morph w' in
    let sframe = r.pl.conn_large_to_small.morph frame in
    (composable p sw sframe /\ op p sframe sw == sw')
  ));
  A.return x'

let ref_upd_act (r: ref 'a 'p) (x: Ghost.erased 'b { ~ (Ghost.reveal x == one 'p) }) (y: Ghost.erased 'b) (f: frame_preserving_upd 'p x y)
: Tot (M.action_except unit Set.empty (hp_of (r `pts_to` x)) (fun _ -> hp_of (r `pts_to` y)))
= M.upd_gen Set.empty r.r  (Ghost.hide (r.pl.conn_small_to_large.morph x)) (Ghost.hide (r.pl.conn_small_to_large.morph y)) (r.pl.conn_lift_frame_preserving_upd (|x, y, restricted_frame_preserving_upd_intro f|))

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
  Classical.forall_intro (is_unit p);
  compatible_refl p y;
  y

let pts_to_view_explicit_witinv
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type u#c)
  (vw: sel_view p c)
: Lemma
  (M.is_witness_invariant (pts_to_view_explicit r vw))
= let aux (x y : Ghost.erased c) (m:M.mem)
  : Lemma
    (requires (M.interp (pts_to_view_explicit r vw x) m /\ M.interp (pts_to_view_explicit r vw y) m))
    (ensures  (x == y))
  =
    let x_ = vw.to_carrier x in
    let y_ = vw.to_carrier y in
    let x' = r.pl.conn_small_to_large.morph x_ in
    let y' = r.pl.conn_small_to_large.morph y_ in
    M.pts_to_join r.r x' y' m;
    let z' = FStar.IndefiniteDescription.indefinite_description_ghost a (fun z' -> compatible r.p x' z' /\ compatible r.p y' z') in
    let frame_x' = FStar.IndefiniteDescription.indefinite_description_ghost a (fun frame_x' -> composable r.p x' frame_x' /\ op r.p frame_x' x' == z') in
    let frame_y' = FStar.IndefiniteDescription.indefinite_description_ghost a (fun frame_y' -> composable r.p y' frame_y' /\ op r.p frame_y' y' == z') in
    let frame_x_ = r.pl.conn_large_to_small.morph frame_x' in
    let frame_y_ = r.pl.conn_large_to_small.morph frame_y' in
    r.p.comm x' frame_x';
    r.pl.conn_large_to_small.morph_compose x' frame_x';
    vw.to_view_frame x (r.pl.conn_large_to_small.morph frame_x');
    r.p.comm y' frame_y';
    r.pl.conn_large_to_small.morph_compose y' frame_y';
    vw.to_view_frame y (r.pl.conn_large_to_small.morph frame_y');
    ()
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (aux x y))
