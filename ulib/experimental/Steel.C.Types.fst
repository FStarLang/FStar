module Steel.C.Types
open Steel.C.Model.PCM

#set-options "--smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"

let prod_perm
  p1 p2
= let w = let open FStar.Real in P.MkPerm?.v p1 *. P.MkPerm?.v p2 in
  assert (let open FStar.Real in (p2 `P.lesser_equal_perm` P.full_perm ==> w <=. P.MkPerm?.v p1 *. 1.0R));
  P.MkPerm w

noeq
type typedef (t: Type0) : Type u#1 = {
  pcm: pcm t;
  fractionable: (t -> Tot prop);
  mk_fraction: (
    (x: t) ->
    (p: P.perm) ->
    Pure t
    (requires (fractionable x))
    (ensures (fun y -> p `P.lesser_equal_perm` P.full_perm ==> fractionable y))
  );
  mk_fraction_full: (
    (x: t) ->
    Lemma
    (requires (fractionable x))
    (ensures (fractionable x /\ mk_fraction x P.full_perm == x))
  );
  mk_fraction_compose: (
    (x: t) ->
    (p1: P.perm) ->
    (p2: P.perm) ->
    Lemma
    (requires (fractionable x /\ p1 `P.lesser_equal_perm` P.full_perm /\ p2 `P.lesser_equal_perm` P.full_perm))
    (ensures (mk_fraction (mk_fraction x p1) p2 == mk_fraction x (p1 `prod_perm` p2)))
  );
  fractionable_one: squash (fractionable (one pcm));
  mk_fraction_one: (
    (p: P.perm) ->
    Lemma
    (mk_fraction (one pcm) p == one pcm)
  );
  uninitialized: (y: t { exclusive pcm y });
  mk_fraction_split: (
    (v: t) ->
    (p1: P.perm) ->
    (p2: P.perm) ->
    Lemma
    (requires (fractionable v /\ (p1 `P.sum_perm` p2) `P.lesser_equal_perm` P.full_perm))
    (ensures (
      composable pcm (mk_fraction v p1) (mk_fraction v p2)
    ))
  );
  mk_fraction_join: (
    (v: t) ->
    (p1: P.perm) ->
    (p2: P.perm) ->
    Lemma
    (requires (
      fractionable v /\
      composable pcm (mk_fraction v p1) (mk_fraction v p2)
    ))
    (ensures (
      op pcm (mk_fraction v p1) (mk_fraction v p2) == mk_fraction v (p1 `P.sum_perm` p2)
    ))
  );
}

let fractionable td x = td.fractionable x
let mk_fraction td x p = td.mk_fraction x p
let mk_fraction_full td x = td.mk_fraction_full x
let mk_fraction_compose td x p1 p2 = td.mk_fraction_compose x p1 p2

let full td v = exclusive td.pcm v

let uninitialized td = td.uninitialized

let unknown td = one td.pcm

let mk_fraction_unknown td p = td.mk_fraction_one p

module R = Steel.C.Model.Ref

let ptr td = R.ptr td.pcm
let null _ = R.null _

let _pts_to r v = hp_of (R.pts_to r v)

#restart-solver
let mk_fraction_split_gen
  #_ #_ #td r v p p1 p2
=
  td.mk_fraction_split v p1 p2;
  td.mk_fraction_join v p1 p2;
  rewrite_slprop
    (pts_to _ _)
    (R.pts_to r (op td.pcm (td.mk_fraction v p1) (td.mk_fraction v p2)))
    (fun _ -> ());
  R.split r _ (td.mk_fraction v p1) (td.mk_fraction v p2);
  rewrite_slprop
    (R.pts_to r (td.mk_fraction v p1))
    (pts_to r (mk_fraction td v p1))
    (fun _ -> ());
  rewrite_slprop
    (R.pts_to r (td.mk_fraction v p2))
    (pts_to r (mk_fraction td v p2))
    (fun _ -> ())

let mk_fraction_join
  #_ #_ #td r v p1 p2
=
  rewrite_slprop
    (pts_to r (mk_fraction td v p1))
    (R.pts_to r (td.mk_fraction v p1))
    (fun _ -> ());
  rewrite_slprop
    (pts_to r (mk_fraction td v p2))
    (R.pts_to r (td.mk_fraction v p2))
    (fun _ -> ());
  R.gather r (td.mk_fraction v p1) (td.mk_fraction v p2);
  td.mk_fraction_join v p1 p2;
  rewrite_slprop
    (R.pts_to _ _)
    (pts_to _ _)
    (fun _ -> ())

module F = Steel.C.Model.Frac
module U = Steel.C.Model.Uninit

let scalar_t t = U.uninit_t (F.fractional t)

let scalar_fractionable
  (#t: Type)
  (s: scalar_t t)
: GTot prop
= match s with
  | U.InitOrUnit (Some (_, p)) -> (p `P.lesser_equal_perm` P.full_perm) == true
  | U.InitOrUnit None -> True
  | _ -> False

[@@noextract_to "krml"] // proof-only
let scalar_mk_fraction
  (#t: Type)
  (x: scalar_t t)
  (p: P.perm)
: Pure (scalar_t t)
    (requires (scalar_fractionable x))
    (ensures (fun y -> p `P.lesser_equal_perm` P.full_perm ==> scalar_fractionable y))
= match x with
  | U.InitOrUnit (Some (v, p')) ->
    U.InitOrUnit (Some (v, p `prod_perm` p'))
  | _ -> x

#restart-solver
let scalar t = {
  pcm = U.pcm_uninit F.pcm_frac;
  fractionable = scalar_fractionable #t;
  mk_fraction = scalar_mk_fraction #t;
  mk_fraction_full = (fun x ->
    match x with
    | U.InitOrUnit (Some (v, p)) ->
      assert_norm ((P.full_perm `prod_perm` p).v == (let open FStar.Real in 1.0R *. p.v));
      assert (P.full_perm `prod_perm` p == p)
    | _ -> ()
  );
  mk_fraction_compose = (fun w p1 p2 ->
    match w with
    | U.InitOrUnit (Some (v, p)) ->
      assert_norm (let open FStar.Real in ((p1 `prod_perm` p2) `prod_perm` p).v == (p1.v *. p2.v) *. p.v);
      assert_norm (let open FStar.Real in (p2 `prod_perm` (p1 `prod_perm` p)).v == p2.v *. (p1.v *. p.v));
      assert ((p1 `prod_perm` p2) `prod_perm` p == p2 `prod_perm` (p1 `prod_perm` p))
    | _ -> ()
  );
  fractionable_one = ();
  mk_fraction_one = (fun _ -> ());
  uninitialized = U.Uninitialized;
  mk_fraction_split = (fun w p1 p2 ->
    match w with
    | U.InitOrUnit (Some (v, p)) ->
      assert_norm (((p1 `P.sum_perm` p2) `prod_perm` p).v == (let open FStar.Real in (p1.v +. p2.v) *. p.v));
      assert_norm (((p1 `prod_perm` p) `P.sum_perm` (p2 `prod_perm` p)).v == (let open FStar.Real in (p1.v *. p.v) +. (p2.v *. p.v)));
      assert ((p1 `P.sum_perm` p2) `prod_perm` p == (p1 `prod_perm` p) `P.sum_perm` (p2 `prod_perm` p));
      assert (composable (U.pcm_uninit F.pcm_frac) (scalar_mk_fraction w p1) (scalar_mk_fraction w p2));
()   //   assert (op (U.pcm_uninit F.pcm_frac) (scalar_mk_fraction w p1) (scalar_mk_fraction w p2) == scalar_mk_fraction w (p1 `P.sum_perm` p2))
    | _ -> ()
  );
  mk_fraction_join = (fun w p1 p2 ->
    match w with
    | U.InitOrUnit (Some (v, p)) ->
      assert_norm (((p1 `P.sum_perm` p2) `prod_perm` p).v == (let open FStar.Real in (p1.v +. p2.v) *. p.v));
      assert_norm (((p1 `prod_perm` p) `P.sum_perm` (p2 `prod_perm` p)).v == (let open FStar.Real in (p1.v *. p.v) +. (p2.v *. p.v)));
      assert ((p1 `P.sum_perm` p2) `prod_perm` p == (p1 `prod_perm` p) `P.sum_perm` (p2 `prod_perm` p))
    | _ -> ()
  );
}

let mk_scalar v = U.InitOrUnit (Some (v, P.full_perm))

let mk_scalar_fractionable v p = ()

let mk_scalar_inj v1 v2 p1 p2 = ()

let scalar_unique
  v1 v2 p1 p2 r
=
  rewrite_slprop
    (pts_to r (mk_fraction (scalar _) (mk_scalar v1) p1))
    (R.pts_to r (U.InitOrUnit (Some (v1, p1))))
    (fun _ -> ());
  rewrite_slprop
    (pts_to r (mk_fraction (scalar _) (mk_scalar v2) p2))
    (R.pts_to r (U.InitOrUnit (Some (v2, p2))))
    (fun _ -> ());
  R.gather r (U.InitOrUnit (Some (v1, p1))) (U.InitOrUnit (Some (v2, p2)));
  R.split r _ (U.InitOrUnit (Some (v1, p1))) (U.InitOrUnit (Some (v2, p2)));
  rewrite_slprop
    (R.pts_to r (U.InitOrUnit (Some (v1, p1))))
    (pts_to r (mk_fraction (scalar _) (mk_scalar v1) p1))
    (fun _ -> ());
  rewrite_slprop
    (R.pts_to r (U.InitOrUnit (Some (v2, p2))))
    (pts_to r (mk_fraction (scalar _) (mk_scalar v2) p2))
    (fun _ -> ())

let read0
  #t #v #p r
=
  rewrite_slprop
    (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
    (R.pts_to r (U.InitOrUnit (Some (Ghost.reveal v, p))))
    (fun _ -> ());
  let v' = R.ref_read r in
  rewrite_slprop
    (R.pts_to r (U.InitOrUnit (Some (Ghost.reveal v, p))))
    (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
    (fun _ -> ());
  let U.InitOrUnit (Some (v0, _)) = v' in
  return v0

let write
  #t #v r v'
=
  rewrite_slprop
    (pts_to r v)
    (R.pts_to r v)
    (fun _ -> ());
  R.ref_upd r _ _ (R.base_fpu _ _ (U.InitOrUnit (Some (v', P.full_perm))));
  rewrite_slprop
    (R.pts_to r _)
    (pts_to _ _)
    (fun _ -> ())

let field_t_nil = unit
let field_t_cons _ _ _ = unit

irreducible let norm_field_attr = ()

let define_struct0 _ _ _ = unit

module S = Steel.C.Model.Struct

[@@noextract_to "krml"] // proof-only
let struct_field_pcm
  (#tf: Type0)
  (fields: field_description_t tf)
  (f: field_t fields)
: Tot (pcm (fields.fd_type f))
= (fields.fd_typedef f).pcm

module FX = FStar.FunctionalExtensionality

let struct_t0 _ n fields =
  FX.restricted_t (field_t fields) fields.fd_type

[@@noextract_to "krml"] // proof-only
let struct_pcm
  (tn: Type0) (#tf: Type0) (n: string) (fields: field_description_t tf)
: Tot (pcm (struct_t0 tn n fields))
= S.prod_pcm (struct_field_pcm fields)

[@@noextract_to "krml"] // proof-only
let t_struct_set_field
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: field_description_t tf) (f: field_t fields) (v: fields.fd_type f) (s: struct_t0 tn n fields)
: Tot (struct_t0 tn n fields)
= FX.on_dom (field_t fields) (fun f' -> if f = f' then v else s f')

let struct_set_field = t_struct_set_field

let struct_get_field
  s field
= s field

let struct_eq
  s1 s2
= s1 `FX.feq` s2

let struct_eq_intro
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s1 s2: struct_t0 tn n fields)
  (prf: (
    (f: field_t fields) ->
    Lemma
    (s1 f == s2 f)
  ))
: Lemma
  (s1 == s2)
= Classical.forall_intro prf;
  assert (s1 `FX.feq` s2)

let struct_get_field_same
  s field v
= ()

let struct_get_field_other
  s field v field'
= ()

let struct_fractionable
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: field_description_t tf)
  (s: struct_t0 tn n fields)
: GTot prop
= forall (f: field_t fields) . (fields.fd_typedef f).fractionable (s f)

[@@noextract_to "krml"] // proof-only
let struct_mk_fraction
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: field_description_t tf)
  (s: struct_t0 tn n fields)
  (p: P.perm)
: Pure (struct_t0 tn n fields)
  (requires (struct_fractionable s))
  (ensures (fun s' -> p `P.lesser_equal_perm` P.full_perm ==> struct_fractionable s'))
= FX.on_dom (field_t fields) (fun f -> (fields.fd_typedef f).mk_fraction (s f) p)

[@@noextract_to "krml"] // proof-only
let struct_uninitialized
  (tn: Type0) (#tf: Type0) (n: string) (fields: field_description_t tf)
: Tot (struct_t0 tn n fields)
= FX.on_dom (field_t fields) (fun f -> (fields.fd_typedef f).uninitialized <: fields.fd_type f)

let struct0
  tn n fields
= {
  pcm = struct_pcm tn n fields;
  fractionable = struct_fractionable;
  mk_fraction = struct_mk_fraction;
  mk_fraction_full = (fun x ->
    struct_eq_intro (struct_mk_fraction x P.full_perm) x (fun f ->
      (fields.fd_typedef f).mk_fraction_full (x f)
    )
  );
  mk_fraction_compose = (fun x p1 p2 ->
    struct_eq_intro (struct_mk_fraction (struct_mk_fraction x p1) p2) (struct_mk_fraction x (p1 `prod_perm` p2)) (fun f ->
      (fields.fd_typedef f).mk_fraction_compose (x f) p1 p2
    )
  );
  fractionable_one = ();
  mk_fraction_one = (fun p ->
    struct_eq_intro (struct_mk_fraction (one (struct_pcm tn n fields)) p) (one (struct_pcm tn n fields)) (fun f ->
      (fields.fd_typedef f).mk_fraction_one p
    )
  );
  uninitialized = struct_uninitialized _ _ _;
  mk_fraction_split = (fun v p1 p2 ->
    let prf
      (f: field_t fields)
    : Lemma
      (composable (fields.fd_typedef f).pcm (mk_fraction (fields.fd_typedef f) (v f) p1) (mk_fraction (fields.fd_typedef f) (v f) p2))
    = (fields.fd_typedef f).mk_fraction_split (v f) p1 p2
    in
    Classical.forall_intro prf
  );
  mk_fraction_join = (fun v p1 p2 ->
    struct_eq_intro (op (struct_pcm tn n fields) (struct_mk_fraction v p1) (struct_mk_fraction v p2)) (struct_mk_fraction v (p1 `P.sum_perm` p2)) (fun f ->
      (fields.fd_typedef f).mk_fraction_join (v f) p1 p2
    )
  );
}

let struct_get_field_unknown
  tn n fields field
= ()

let struct_get_field_uninitialized
  tn n fields field
= ()

let g_struct_field
  #_ #_ #_ #fields r field
= R.ref_focus r (S.struct_field (struct_field_pcm fields) field)

#push-options "--z3rlimit 16"

let ghost_struct_field
  #_ #tn #_ #n #fields #v r field
= rewrite_slprop
    (pts_to r v)
    (R.pts_to r v)
    (fun _ -> ());
  let prf
    (f': field_t fields)
    (x: (fields.fd_type f'))
  : Lemma
    (let p = (fields.fd_typedef f').pcm in
      composable p x (one p) /\
      op p x (one p) == x
    )
  = is_unit (fields.fd_typedef f').pcm x
  in
  Classical.forall_intro_2 prf;
  let v' = struct_set_field field (unknown (fields.fd_typedef field)) v in
  let vf = S.field_to_struct_f (struct_field_pcm fields) field (struct_get_field v field) in
  assert (composable (struct_pcm tn n fields) v' vf);
  assert (op (struct_pcm tn n fields) v' vf `FX.feq` v);
  R.split r _ v' vf;
  R.gfocus r (S.struct_field (struct_field_pcm fields) field) vf (struct_get_field v field);
  rewrite_slprop
    (R.pts_to r _)
    (pts_to r _)
    (fun _ -> ());
  rewrite_slprop
    (R.pts_to _ _)
    (pts_to (g_struct_field r field) _)
    (fun _ -> ())

[@@noextract_to "krml"] // primitive
let struct_field'
  (#tn: Type0)
  (#tf: Type0)
  (#opened: _)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
: SteelAtomicBase (ref (fields.fd_typedef field)) false opened Unobservable
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (struct_get_field v field))
    (fun _ -> True)
    (fun _ r' _ -> r' == g_struct_field r field)
= rewrite_slprop
    (pts_to r v)
    (R.pts_to r v)
    (fun _ -> ());
  let prf
    (f': field_t fields)
    (x: (fields.fd_type f'))
  : Lemma
    (let p = (fields.fd_typedef f').pcm in
      composable p x (one p) /\
      op p x (one p) == x
    )
  = is_unit (fields.fd_typedef f').pcm x
  in
  Classical.forall_intro_2 prf;
  let v' = Ghost.hide (struct_set_field field (unknown (fields.fd_typedef field)) v) in
  let vf = Ghost.hide (S.field_to_struct_f (struct_field_pcm fields) field (struct_get_field v field)) in
  assert (composable (struct_pcm tn n fields) v' vf);
  assert (op (struct_pcm tn n fields) v' vf `FX.feq` v);
  R.split r _ v' vf;
  let r' = R.focus r (S.struct_field (struct_field_pcm fields) field) vf (struct_get_field v field) in
  rewrite_slprop
    (R.pts_to r _)
    (pts_to r _)
    (fun _ -> ());
  rewrite_slprop
    (R.pts_to _ _)
    (pts_to r' _)
    (fun _ -> ());
  return r'

let struct_field0
  t' r field td'
=
  let r' = struct_field' r field in
  let res : ref td' = r' in
  change_equal_slprop (pts_to r' _) (pts_to res _);
  return res

let unstruct_field
  #_ #tn #_ #n #fields #v r field #v' r'
= rewrite_slprop
    (pts_to r v)
    (R.pts_to r v)
    (fun _ -> ());
  rewrite_slprop
    (pts_to r' v')
    (R.pts_to r' v')
    (fun _ -> ());
  let prf
    (f': field_t fields)
    (x: (fields.fd_type f'))
  : Lemma
    (let p = (fields.fd_typedef f').pcm in
      composable p x (one p) /\
      op p x (one p) == x
    )
  = is_unit (fields.fd_typedef f').pcm x
  in
  Classical.forall_intro_2 prf;
  let vf = S.field_to_struct_f (struct_field_pcm fields) field v' in
  assert (composable (struct_pcm tn n fields) v vf);
  assert (op (struct_pcm tn n fields) v vf `FX.feq` struct_set_field field v' v);
  R.unfocus r' r (S.struct_field (struct_field_pcm fields) field) _;
  R.gather r v _;
  rewrite_slprop
    (R.pts_to r _)
    (pts_to r _)
    (fun _ -> ())

#pop-options

let fractionable_struct _ = ()
let mk_fraction_struct _ _ _ = ()

let full_struct
  #tn #_ #n #fields s
=
  let is_unit'
    (f': field_t fields)
    (x: (fields.fd_type f'))
  : Lemma
    (let p = (fields.fd_typedef f').pcm in
      composable p x (one p) /\
      op p x (one p) == x
    )
  = is_unit (fields.fd_typedef f').pcm x
  in
  Classical.forall_intro_2 is_unit';
  let prf
    (field: field_t fields)
  : Lemma
    (requires (full (struct0 tn n fields) s))
    (ensures (full (fields.fd_typedef field) (struct_get_field s field)))
  = let prf'
      (x: fields.fd_type field)
    : Lemma
      (requires (composable (fields.fd_typedef field).pcm (struct_get_field s field) x))
      (ensures (x == one (fields.fd_typedef field).pcm))
    = let s' = struct_set_field field x (one (struct_pcm tn n fields)) in
      assert (composable (struct_pcm tn n fields) s s')
    in
    Classical.forall_intro (Classical.move_requires prf')
  in
  Classical.forall_intro (Classical.move_requires prf)
