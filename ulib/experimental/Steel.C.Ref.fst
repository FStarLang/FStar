module Steel.C.Ref
module P = FStar.PCM
module U = Steel.C.Universe
open FStar.FunctionalExtensionality

module M = Steel.Memory
module R = Steel.PCMReference
module GHR = Steel.GhostPCMReference
module RO = Steel.PCMReadOnly

#push-options "--print_universes"

let is_base_type
  (r: GHR.ref _ (RO.pcm_readonly #Type0))
  (i: M.iname)
  (t0: Type)
: Tot prop
= (let open Steel.Effect.Atomic in ( >--> ))
    i
    (GHR.pts_to r (Some t0))

let has_base_type
  (r: GHR.ref _ (RO.pcm_readonly #Type0))
  (i: M.iname)
: Tot prop
= exists (t0: Type) . is_base_type r i t0

let has_base_type_intro
  (r: GHR.ref _ (RO.pcm_readonly #Type0))
  (i: M.iname)
  (t0: Type)
: Lemma
  (requires ((let open Steel.Effect.Atomic in ( >--> )) i (GHR.pts_to r (Some t0))))
  (ensures (has_base_type r i))
= ()

let get_base_type
  (r: GHR.ref _ (RO.pcm_readonly #Type0))
  (i: M.iname)
: Pure Type
    (requires (has_base_type r i))
    (ensures (fun t0 -> is_base_type r i t0))
= FStar.IndefiniteDescription.indefinite_description_ghost Type (fun t0 -> is_base_type r i t0)

let with_invariant_g_f (#a:Type)
                     (#fp:A.vprop)
                     (#fp':a -> A.vprop)
                     (#opened_invariants:M.inames)
                     (#p:A.vprop)
                     (i:A.inv p{not (A.mem_inv opened_invariants i)})
                     (f:unit -> A.SteelGhostT a (A.add_inv opened_invariants i)
                                         (p `A.star` fp)
                                         (fun x -> p `A.star` fp' x))
  : A.SteelGhostF a opened_invariants fp fp' (fun _ -> True) (fun _ _ _ -> True)
= A.with_invariant_g i f

let has_base_type_idem
  (#opened: M.inames)
  (r: GHR.ref _ (RO.pcm_readonly #Type0))
  (i: M.iname)
  (v: Type0)
  (sq: squash (
    not (A.mem_inv opened i) /\
    has_base_type r i
  ))
: A.SteelGhostT (squash (v == get_base_type r i)) opened
    (GHR.pts_to r (Some v))
    (fun _ -> GHR.pts_to r (Some v))
= with_invariant_g_f
    #(squash (v == get_base_type r i))
    #(GHR.pts_to r (Some v))
    #(fun _ -> GHR.pts_to r (Some v))
    #_
    #(GHR.pts_to r (Some (get_base_type r i)))
    i
    (fun _ ->
      GHR.gather r (Some v) _;
      GHR.share r _ (Some v) (Some (get_base_type r i))
    )

noeq type ref0 (b: Type u#b) : Type u#b = {
  base_type: GHR.ref _ (RO.pcm_readonly #Type0);
  base_inv: Ghost.erased M.iname;
  base_has_type: squash (has_base_type base_type base_inv);
  p: pcm (get_base_type base_type base_inv);
  q: pcm b;
  pl: connection p q;
  r: M.ref (U.raise_t (get_base_type base_type base_inv)) (fstar_pcm_of_pcm (U.raise_pcm p));
}

noeq type ptr' (b: Type u#b) : Type u#b =
  | NonNull: (v: ref0 b) -> ptr' b
  | Null: (v: pcm b) -> ptr' b

let pcm_of_ptr'
  (#b: Type u#b)
  (r: ptr' b)
: Tot (pcm b)
= if Null? r then Null?.v r else (NonNull?.v r).q

let ptr #b p = (r: ptr' b { pcm_of_ptr' r == p })

let null p = Null p

let ptr_is_null p = Null? p

let raise_p
  (#b: Type u#b)
  (r: ptr' b { NonNull? r})
: Tot (pcm (U.raise_t u#0 u#1 (get_base_type (NonNull?.v r).base_type (NonNull?.v r).base_inv)))
= U.raise_pcm (NonNull?.v r).p

let base_of
  (#b: Type u#b)
  (r: ptr' b { NonNull? r })
: Tot (M.ref _ (fstar_pcm_of_pcm (raise_p r)))
= (NonNull?.v r).r

let lower_conn
  (#b: Type u#b)
  (r: ptr' b { NonNull? r})
: Tot (connection (raise_p r) (NonNull?.v r).p)
= connection_of_isomorphism (isomorphism_inverse (U.raise_pcm_isomorphism u#0 u#1 (NonNull?.v r).p))

let raise_pl
  (#b: Type u#b)
  (r: ptr' b {NonNull? r})
: Tot (connection (raise_p r) (NonNull?.v r).q)
= lower_conn r `connection_compose` (NonNull?.v r).pl

let mpts_to (#a: Type u#1) (#p: P.pcm a) (r: Steel.Memory.ref a p) ([@@@smt_fallback] v: a) = Steel.PCMReference.pts_to r v

[@@__reduce__]
let pts_to0
  (#b: Type u#b) (#p: pcm b)
  (r: ref p) (v: b)
: Tot vprop
= mpts_to (base_of r) ((raise_pl r).conn_small_to_large.morph v) `star`
  GHR.pts_to (NonNull?.v r).base_type (Some (get_base_type (NonNull?.v r).base_type (NonNull?.v r).base_inv))

let pts_to r v = pts_to0 r v

let t_ref_focus
  (#b:Type) (#c:Type) (#p: pcm b)
  (r: ref p) (#q: pcm c) (l: connection p q)
: Tot (ref q)
= let NonNull r = r in
  NonNull ({r with p = r.p; pl = connection_compose r.pl l; q = q})

let ref_focus r l = t_ref_focus r l

let ref_focus_id r = connection_compose_id_right (NonNull?.v r).pl

let ref_focus_comp r l m
= connection_compose_assoc (NonNull?.v r).pl l m

(* freeable r if and only if r is a "base" reference, i.e. its connection path is empty *)

let freeable #b #p r =
  let NonNull r = r in
  get_base_type r.base_type r.base_inv == b /\
  r.q == r.p /\
  r.pl == connection_id _

#push-options "--z3rlimit 32"
#restart-solver

let ref_alloc #a pcm v =
  let r : Steel.Memory.ref (U.raise_t a) (fstar_pcm_of_pcm (U.raise_pcm pcm)) = R.alloc (U.raise_val v) in
  let g: GHR.ref _ (RO.pcm_readonly #Type0) = GHR.alloc (Some a) in
  GHR.share g (Some a) (Some a) (Some a);
  let i = A.new_invariant (GHR.pts_to g (Some a)) in
  has_base_type_intro g i a;
  has_base_type_idem g i _ ();
  let p : ref pcm = NonNull ({
    base_type = g;
    base_inv = i;
    base_has_type = ();
    p = pcm;
    q = pcm;
    pl = connection_id _;
    r = r;
  })
  in
  A.change_equal_slprop
    (mpts_to r (U.raise_val v))
    (mpts_to (base_of p) ((raise_pl p).conn_small_to_large.morph v));
  A.change_equal_slprop
    (GHR.pts_to g _)
    (GHR.pts_to (NonNull?.v p).base_type (Some (get_base_type (NonNull?.v p).base_type (NonNull?.v p).base_inv)));
  A.change_equal_slprop
    (pts_to0 p v)
    (pts_to p v);
  A.return p

let ref_free #b #p #x r =
  // TODO: use Steel.PCMReference.free, but we are blocked by (p.refine (one p)), which we explicitly excluded in Steel.C.PCM
  A.drop (pts_to _ _)

#pop-options

let gfocus r l s x =
  connection_compose_assoc (lower_conn r) (NonNull?.v r).pl l;
  A.change_equal_slprop
    (r `pts_to` s)
    (ref_focus r l `pts_to` x)

let focus r l s x =
  let r' = t_ref_focus r l in
  gfocus r l s x;
  A.change_equal_slprop
    (ref_focus r l `pts_to` x)
    (r' `pts_to` x);
  A.return r'

let unfocus r r' l x =
  connection_compose_assoc (lower_conn r') (NonNull?.v r').pl l;
  A.change_equal_slprop
    (r `pts_to` x)
    (r' `pts_to` l.conn_small_to_large.morph x)

let read_only_share
  (#a: Type)
  (#opened: _)
  (#v: a)
  (r: GHR.ref _ (RO.pcm_readonly #a))
: A.SteelGhostT unit opened
    (GHR.pts_to r (Some v))
    (fun _ -> GHR.pts_to r (Some v) `star` GHR.pts_to r (Some v))
= GHR.share r _ (Some v) (Some v)

#push-options "--z3rlimit 16"
#restart-solver

let split r xy x y =
  let c = raise_pl r in
  let xy2 = (c.conn_small_to_large.morph xy) in
  let x2 = (c.conn_small_to_large.morph x) in
  let y2 = (c.conn_small_to_large.morph y) in
  assert (P.composable (fstar_pcm_of_pcm (raise_p r)) x2 y2);
  A.change_equal_slprop (r `pts_to` xy) (r `pts_to0` xy);
  A.change_equal_slprop
    (_ `mpts_to` _)
    (base_of r `mpts_to` xy2);
  R.split (base_of r)
    xy2
    x2
    y2;
  read_only_share (NonNull?.v r).base_type;
  A.change_equal_slprop
    (mpts_to (base_of r) x2 `star` GHR.pts_to _ _)
    (r `pts_to` x);
  A.change_equal_slprop
    (mpts_to (base_of r) y2 `star` GHR.pts_to _ _)
    (r `pts_to` y)

let mgather
  (#inames: _) (#a:Type) (#p:P.pcm a)
  (r:Steel.Memory.ref a p) (v0:Ghost.erased a) (v1:Ghost.erased a)
: A.SteelGhostT (_:unit{P.composable p v0 v1}) inames
    (mpts_to r v0 `star` mpts_to r v1)
    (fun _ -> mpts_to r (P.op p v0 v1))
= Steel.PCMReference.gather r v0 v1

let gather #inames #b #p r x y =
  let c = raise_pl r in
  let x2 = (c.conn_small_to_large.morph x) in
  let y2 = (c.conn_small_to_large.morph y) in
  A.change_equal_slprop (r `pts_to` x) (r `pts_to0` x);
  A.change_equal_slprop (mpts_to (base_of r) _) (mpts_to (base_of r) x2);
  A.change_equal_slprop (r `pts_to` y) (r `pts_to0` y);
  mgather (base_of r) x2 _;
  GHR.gather (NonNull?.v r).base_type _ _;
  assert (composable (raise_p r) x2 y2);
  assert (
    let x' = c.conn_large_to_small.morph x2 in
    let y' = c.conn_large_to_small.morph y2 in
    composable p x' y' /\
    x == x' /\ y == y'
  );
  A.change_equal_slprop
    (mpts_to _ _ `star` GHR.pts_to _ _)
    (r `pts_to` op p x y)

let ref_read
  #_ #p #x r
= let w = Ghost.hide ((raise_pl r).conn_small_to_large.morph x) in
  A.change_equal_slprop (r `pts_to` x) (r `pts_to0` x);
  A.change_equal_slprop (mpts_to _ _) (mpts_to (base_of r) (Ghost.reveal w));
  let w' = R.read (base_of r) w in
  A.change_equal_slprop (mpts_to _ _ `star` GHR.pts_to _ _) (r `pts_to` x);
  let x' = (raise_pl r).conn_large_to_small.morph w' in
  compatible_morphism (raise_pl r).conn_large_to_small w w';
  assert (compatible p x x');
  A.return x'

let ref_upd #b #p r x y f =
  let c = raise_pl r in
  let x' = Ghost.hide (c.conn_small_to_large.morph x) in
  let y' = Ghost.hide (c.conn_small_to_large.morph y) in
  A.change_equal_slprop (r `pts_to` x) (r `pts_to0` x);
  A.change_equal_slprop (mpts_to _ _) (mpts_to (base_of r) (Ghost.reveal x'));
  R.upd_gen (base_of r) x' y' (fstar_fpu_of_fpu (raise_p r) x' y' (mk_restricted_frame_preserving_upd (c.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = restricted_frame_preserving_upd_intro f; }) )));
  A.change_equal_slprop (mpts_to _ _ `star` GHR.pts_to _ _) (r `pts_to` y)

let base_fpu p x y =
  fun _ ->
  compatible_refl p y;
  y

let pts_to_view_explicit
  (#b: Type u#b) (#p: pcm b)
  (r: ref p)
  (#c: Type u#c)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
  (v: Ghost.erased c)
: Tot M.slprop
= hp_of (pts_to r (vw.to_carrier v))

let pts_to_view_explicit_witinv
  (#b: Type u#b) (#p: pcm b)
  (r: ref p)
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
    M.pts_to_join (base_of r) x' y' m;
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
  r vw
= M.h_exists (pts_to_view_explicit r vw)

let pts_to_view_sel'
  (#b: Type u#b) (#p: pcm b)
  (r: ref p)
  (#c: Type0)
  (#can_view_unit: bool)
  (vw: sel_view p c can_view_unit)
: Tot (selector' c (pts_to_view_sl r vw))
= fun h ->
  let x = M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) h in
  Ghost.reveal (Ghost.reveal x)

let pts_to_view_depends_only_on
  (#b: Type u#b) (#p: pcm b)
  (r: ref p)
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
  (#b: Type u#b) (#p: pcm b)
  (r: ref p)
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
  r vw
= Classical.forall_intro_2 (pts_to_view_depends_only_on r vw);
  Classical.forall_intro (pts_to_view_depends_only_on_core r vw);
  pts_to_view_sel' r vw

let pts_to_view_intro_lemma
  (#b: Type u#b) (#p: pcm b)
  (r: ref p)
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
  r x vw y
= A.change_slprop_2
    (pts_to r x)
    (pts_to_view r vw)
    y
    (fun m ->
      pts_to_view_intro_lemma r x vw y m
    )

let pts_to_view_elim_lemma
  (#b: Type u#b) (#p: pcm b)
  (r: ref p)
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
  (#b: Type u#b) (#p: pcm b)
  (r: ref p)
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

let ref_read_sel
  (#b: Type u#b) (#p: pcm b)
  (r: ref p)
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
  (#b: Type u#b) (#p: pcm b)
  (r: ptr p)
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
  (#b: Type u#b) (#p: pcm b)
  (r: ptr p)
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
  (#b: Type u#b) (#p: pcm b)
  (r: ptr p)
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
  (#b: Type u#b) (#p: pcm b)
  (r: ptr p)
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
  #_ #b #p #c vw
=
  A.intro_vrewrite emp (fun _ -> None <: option c);
  A.change_equal_slprop
    (emp `vrewrite` (fun _ -> None <: option c))
    (pts_to_view_or_null0 (null p) vw);
  A.change_slprop_rel
    (pts_to_view_or_null0 (null p) vw)
    (pts_to_view_or_null (null p) vw)
    (fun x y -> x == y)
    (fun _ -> ())

let elim_pts_to_view_or_null_null
  #_ #b #p #c vw
=
  A.change_slprop_rel
    (pts_to_view_or_null (null p) vw)
    (pts_to_view_or_null0 (null p) vw)
    (fun x y -> x == y)
    (fun _ -> ());
  A.change_equal_slprop
    (pts_to_view_or_null0 (null p) vw)
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
