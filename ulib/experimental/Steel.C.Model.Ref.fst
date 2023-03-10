module Steel.C.Model.Ref
module P = FStar.PCM
module U = Steel.C.Model.Universe
open FStar.FunctionalExtensionality

friend Steel.C.Model.Ref.Base

let pts_to_view_explicit
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type u#c)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
  (v: Ghost.erased c)
: Tot M.slprop
= hp_of (pts_to r (vw.to_carrier v))

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
    M.pts_to_join (NonNull?.v r).r x' y' m;
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

let pts_to_view_sl
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type u#c)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: Tot M.slprop
= M.h_exists (pts_to_view_explicit r vw)


let pts_to_view_sel'
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: Tot (selector' c (pts_to_view_sl r vw))
= fun h ->
  let x = M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) h in
  Ghost.reveal (Ghost.reveal x)

let pts_to_view_depends_only_on
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
  (m0:M.hmem (pts_to_view_sl r vw)) (m1:M.mem{M.disjoint m0 m1})
: Lemma (pts_to_view_sel' r vw m0 == pts_to_view_sel' r vw (M.join m0 m1))
= let x = Ghost.reveal (M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) m0) in
  let y = Ghost.reveal (M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) (M.join m0 m1)) in
  pts_to_view_explicit_witinv r vw;
  M.elim_wi (pts_to_view_explicit r vw) x y (M.join m0 m1)

let pts_to_view_depends_only_on_core
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
  (m0:M.hmem (pts_to_view_sl r vw))
: Lemma (pts_to_view_sel' r vw m0 == pts_to_view_sel' r vw (M.core_mem m0))
= let x = Ghost.reveal (M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) m0) in
  let y = Ghost.reveal (M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) (M.core_mem m0)) in
  pts_to_view_explicit_witinv r vw;
  M.elim_wi (pts_to_view_explicit r vw) x y (M.core_mem m0)

let pts_to_view_sel
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: Tot (selector c (pts_to_view_sl r vw))
= Classical.forall_intro_2 (pts_to_view_depends_only_on r vw);
  Classical.forall_intro (pts_to_view_depends_only_on_core r vw);
  pts_to_view_sel' r vw

let pts_to_view_intro_lemma
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (x: Ghost.erased b)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
  (y: Ghost.erased c) // necessary because to_view may erase information from x
  (m: M.mem)
: Lemma
  (requires (M.interp (hp_of (pts_to r x)) m) /\ vw.to_carrier y == Ghost.reveal x)
  (ensures (
    M.interp (pts_to_view_sl r vw) m /\
    pts_to_view_sel r vw m == Ghost.reveal y
  )) 
=
  M.intro_h_exists y (pts_to_view_explicit r vw) m;
  pts_to_view_explicit_witinv r vw

let pts_to_view_intro
  (#invs: _)
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (x: Ghost.erased b)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
  (y: Ghost.erased c) // necessary because to_view may erase information from x
: A.SteelGhost unit invs
    (pts_to r x)
    (fun _ -> pts_to_view r vw)
    (fun _ -> vw.to_carrier y == Ghost.reveal x)
    (fun _ _ h' ->
      h' (pts_to_view r vw) == Ghost.reveal y
    )
= A.change_slprop_2
    (pts_to r x)
    (pts_to_view r vw)
    y
    (fun m ->
      pts_to_view_intro_lemma r x vw y m
    )


let pts_to_view_elim_lemma
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
  (m: M.mem)
: Lemma
  (requires (M.interp (pts_to_view_sl r vw) m))
  (ensures (
    M.interp (hp_of (pts_to r (vw.to_carrier (pts_to_view_sel r vw m)))) m
  ))
=
  M.elim_h_exists (pts_to_view_explicit r vw) m;
  pts_to_view_explicit_witinv r vw

/// Introducing a dependent star for [v] and [q]
let intro_vdep2 (#opened:_)
  (v: vprop)
  (q: vprop)
  (p: (t_of v -> Tot vprop))
  (x: t_of v)
: A.SteelGhost unit opened
    (v `star` q)
    (fun _ -> vdep v p)
    (requires (fun h -> h v == x /\ q == p x))
    (ensures (fun h _ h' ->
      let x2 = h' (vdep v p) in
      q == p (h v) /\
      dfst x2 == (h v) /\
      dsnd x2 == (h q)
    ))
=
  A.intro_vdep v q p

let pts_to_view_elim
  (#invs: _)
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: A.SteelGhost (Ghost.erased b) invs
    (pts_to_view r vw)
    (fun res -> pts_to r res)
    (fun _ -> True)
    (fun h res _ ->
      Ghost.reveal res == vw.to_carrier (h (pts_to_view r vw)) /\
      vw.to_view_prop res /\
      True //~ (Ghost.reveal res == one p)
    )
=
  let g : Ghost.erased c = A.gget (pts_to_view r vw) in
  let res : Ghost.erased b = Ghost.hide (vw.to_carrier g) in
  // vw.to_carrier_not_one g;
  A.intro_pure (vw.to_carrier (Ghost.reveal g) == Ghost.reveal res);
  let f (x: t_of (pts_to_view r vw)) : Tot vprop = pure (vw.to_carrier x == Ghost.reveal res) in
  intro_vdep2
    (pts_to_view r vw)
    (pure (vw.to_carrier (Ghost.reveal g) == Ghost.reveal res))
    f
    (Ghost.reveal g);
  A.rewrite_slprop
    (vdep (pts_to_view r vw) f)
    (pts_to r res)
    (fun m ->
      interp_vdep_hp (pts_to_view r vw) f m;
      M.interp_star (hp_of (pts_to_view r vw)) (hp_of (f (sel_of (pts_to_view r vw) m))) m;
      M.pure_interp (vw.to_carrier (sel_of (pts_to_view r vw) m) == Ghost.reveal res) m;
      pts_to_view_elim_lemma r vw m
    );
  res


let compatible_elim'
  (#a: Type u#a)
  (pcm: pcm0 a)
  (x y: a)
  (sq: squash (compatible pcm x y))
: GTot (frame: a {
    composable pcm x frame /\
    op pcm frame x == y
  })
= compatible_elim pcm x y

module STC = Steel.ST.Coercions

let ref_read_sel
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: Steel c
  (pts_to_view r vw)
  (fun _ -> pts_to_view r vw)
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    res == h (pts_to_view r vw) /\
    res == h' (pts_to_view r vw)
  ))
=
  let _v = pts_to_view_elim r vw in
  let v = ref_read r in
  let sq : squash (compatible p _v v) = () in
  let frame = Ghost.hide (compatible_elim' p _v v sq) in
  vw.to_view_frame (vw.to_view _v) frame ;
  let res = vw.to_view v in
  pts_to_view_intro r _v vw res;
  A.return res


// [@@__steel_reduce__; __reduce__]
let pts_to_view_or_null0
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ptr a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: Tot vprop
= if ptr_is_null r
  then (emp `vrewrite` (fun _ -> None <: option c))
  else (pts_to_view r vw `vrewrite` (fun x -> Some x))

let pts_to_view_or_null_sl
  r vw
=
  hp_of (pts_to_view_or_null0 r vw)

let pts_to_view_or_null_sel
  r vw
=
  sel_of (pts_to_view_or_null0 r vw)

let pts_to_view_or_null_prop_null
  (#inames: _)
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ptr a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: A.SteelGhost unit inames
    (pts_to_view_or_null r vw)
    (fun _ -> pts_to_view_or_null r vw)
    (requires fun _ -> Null? r)
    (ensures fun h _ h' ->
      let s = h (pts_to_view_or_null r vw) in
      h' (pts_to_view_or_null r vw) == s /\
      None? s == Null? r
    )
=
  A.change_slprop_rel
    (pts_to_view_or_null r vw)
    (pts_to_view_or_null0 r vw)
    (fun x y -> x == y)
    (fun _ -> ());
  A.change_equal_slprop
    (pts_to_view_or_null0 r vw)
    (emp `vrewrite` (fun _ -> None <: option c));
  A.elim_vrewrite emp (fun _ -> None <: option c);
  A.intro_vrewrite emp (fun _ -> None <: option c);
  A.change_equal_slprop
    (emp `vrewrite` (fun _ -> None <: option c))
    (pts_to_view_or_null0 r vw);  
  A.change_slprop_rel
    (pts_to_view_or_null0 r vw)
    (pts_to_view_or_null r vw)
    (fun x y -> x == y)
    (fun _ -> ())

#push-options "--z3rlimit 16"
#restart-solver
let pts_to_view_or_null_prop_not_null
  (#inames: _)
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ptr a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: A.SteelGhost unit inames
    (pts_to_view_or_null r vw)
    (fun _ -> pts_to_view_or_null r vw)
    (requires fun _ -> NonNull? r)
    (ensures fun h _ h' ->
      let s = h (pts_to_view_or_null r vw) in
      h' (pts_to_view_or_null r vw) == s /\
      None? s == Null? r
    )
=
  A.change_slprop_rel
    (pts_to_view_or_null r vw)
    (pts_to_view_or_null0 r vw)
    (fun x y -> x == y)
    (fun _ -> ());
  A.change_equal_slprop
    (pts_to_view_or_null0 r vw)
    (pts_to_view r vw `vrewrite` (fun x -> Some x));
  A.elim_vrewrite (pts_to_view r vw) (fun x -> Some x);
  A.intro_vrewrite (pts_to_view r vw) (fun x -> Some x);
  A.change_equal_slprop
    (pts_to_view r vw `vrewrite` (fun x -> Some x))
    (pts_to_view_or_null0 r vw);  
  A.change_slprop_rel
    (pts_to_view_or_null0 r vw)
    (pts_to_view_or_null r vw)
    (fun x y -> x == y)
    (fun _ -> ())
#pop-options

let pts_to_view_or_null_prop
  (#inames: _)
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: ptr a p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: A.SteelGhost unit inames
    (pts_to_view_or_null r vw)
    (fun _ -> pts_to_view_or_null r vw)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let s = h (pts_to_view_or_null r vw) in
      h' (pts_to_view_or_null r vw) == s /\
      None? s == Null? r
    )
=
  if Null? r
  then pts_to_view_or_null_prop_null r vw
  else pts_to_view_or_null_prop_not_null r vw

let is_null
  r vw
=
  pts_to_view_or_null_prop r vw;
  A.return (Null? r)

let intro_pts_to_view_or_null_null
  a #b #p #c vw
=
  A.intro_vrewrite emp (fun _ -> None <: option c);
  A.change_equal_slprop
    (emp `vrewrite` (fun _ -> None <: option c))
    (pts_to_view_or_null0 (null a p) vw);
  A.change_slprop_rel
    (pts_to_view_or_null0 (null a p) vw)
    (pts_to_view_or_null (null a p) vw)
    (fun x y -> x == y)
    (fun _ -> ())

let elim_pts_to_view_or_null_null
  a #b #p #c vw
=
  A.change_slprop_rel
    (pts_to_view_or_null (null a p) vw)
    (pts_to_view_or_null0 (null a p) vw)
    (fun x y -> x == y)
    (fun _ -> ());
  A.change_equal_slprop
    (pts_to_view_or_null0 (null a p) vw)
    (emp `vrewrite` (fun _ -> None <: option c));
  A.elim_vrewrite emp (fun _ -> None <: option c)

let intro_pts_to_view_or_null_not_null
  r vw
=
  A.intro_vrewrite
    (pts_to_view r vw)
    (fun x -> Some x);
  A.change_equal_slprop
    (pts_to_view r vw `vrewrite` (fun x -> Some x))
    (pts_to_view_or_null0 r vw);
  A.change_slprop_rel
    (pts_to_view_or_null0 r vw)
    (pts_to_view_or_null r vw)
    (fun x y -> x == y)
    (fun _ -> ())

let elim_pts_to_view_or_null_not_null
  r vw
=
  A.change_slprop_rel
    (pts_to_view_or_null r vw)
    (pts_to_view_or_null0 r vw)
    (fun x y -> x == y)
    (fun _ -> ());
  A.change_equal_slprop
    (pts_to_view_or_null0 r vw)
    (pts_to_view r vw `vrewrite` (fun x -> Some x));
  A.elim_vrewrite
    (pts_to_view r vw)
    (fun x -> Some x)
