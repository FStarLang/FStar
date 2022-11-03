module Steel.C.Types
open Steel.C.Model.PCM

#set-options "--smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"

let prod_perm
  p1 p2
= let w = let open FStar.Real in P.MkPerm?.v p1 *. P.MkPerm?.v p2 in
  assert (let open FStar.Real in (p2 `P.lesser_equal_perm` P.full_perm ==> w <=. P.MkPerm?.v p1 *. 1.0R));
  P.MkPerm w

noeq
type typedef (t: Type0) : Type0 = {
  pcm: pcm t;
  fractionable: (t -> GTot bool);
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
  uninitialized: (y: t {
    exclusive pcm y /\
    fractionable y /\
    p_refine pcm y
  });
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
  mk_fraction_eq_one: (
    (v: t) ->
    (p: P.perm) ->
    Lemma
    (requires (fractionable v /\ mk_fraction v p == one pcm))
    (ensures (v == one pcm))
  );
}

let fractionable td x = td.fractionable x == true
let mk_fraction td x p = td.mk_fraction x p
let mk_fraction_full td x = td.mk_fraction_full x
let mk_fraction_compose td x p1 p2 = td.mk_fraction_compose x p1 p2

let full td v = exclusive td.pcm v /\ p_refine td.pcm v

let uninitialized td = td.uninitialized

let unknown td = one td.pcm

let mk_fraction_unknown td p = td.mk_fraction_one p
let mk_fraction_eq_unknown td v p = td.mk_fraction_eq_one v p

module R = Steel.C.Model.Ref
module TD = Steel.TypeDictionary

noeq
type ref0 : Type0 = {
  dest: TD.token;
  typedef: typedef (TD.type_of_token dest);
  ref: R.ref typedef.pcm;
}

let void_ptr = option ref0
let void_null = None
let type_of_ptr p = TD.type_of_token (Some?.v p).dest
let typedef_of_ptr p = (Some?.v p).typedef

let _pts_to r v = hp_of (R.pts_to (Some?.v r).ref v)

let is_null
  p
= return (None? p)

let freeable
  r
= R.freeable (Some?.v r).ref

let alloc
  #t td
= let r = R.ref_alloc td.pcm td.uninitialized in
  let tok = TD.get_token t in
  let res : ref td = Some ({
    dest = tok;
    typedef = td;
    ref = r;
  })
  in
  rewrite_slprop
    (R.pts_to r _)
    (pts_to_or_null res _)
    (fun _ -> ());
  return res

let free
  #t #td #v r0
= let r : R.ref td.pcm = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 v)
    (R.pts_to r v)
    (fun _ -> ());
  R.ref_free r

#restart-solver
let mk_fraction_split_gen
  #_ #_ #td r0 v p p1 p2
=
  let r = (Some?.v r0).ref in
  td.mk_fraction_split v p1 p2;
  td.mk_fraction_join v p1 p2;
  rewrite_slprop
    (pts_to _ _)
    (R.pts_to r (op td.pcm (td.mk_fraction v p1) (td.mk_fraction v p2)))
    (fun _ -> ());
  R.split r _ (td.mk_fraction v p1) (td.mk_fraction v p2);
  rewrite_slprop
    (R.pts_to r (td.mk_fraction v p1))
    (pts_to r0 (mk_fraction td v p1))
    (fun _ -> ());
  rewrite_slprop
    (R.pts_to r (td.mk_fraction v p2))
    (pts_to r0 (mk_fraction td v p2))
    (fun _ -> ())

let mk_fraction_join
  #_ #_ #td r0 v p1 p2
= let r = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 (mk_fraction td v p1))
    (R.pts_to r (td.mk_fraction v p1))
    (fun _ -> ());
  rewrite_slprop
    (pts_to r0 (mk_fraction td v p2))
    (R.pts_to r (td.mk_fraction v p2))
    (fun _ -> ());
  R.gather r (td.mk_fraction v p1) (td.mk_fraction v p2);
  td.mk_fraction_join v p1 p2;
  rewrite_slprop
    (R.pts_to _ _)
    (pts_to _ _)
    (fun _ -> ())

module F = Steel.C.Model.Frac

let scalar_t t = F.fractional (option t)

let scalar_fractionable
  (#t: Type)
  (s: scalar_t t)
: GTot bool
= match s with
  | Some (_, p) -> p `P.lesser_equal_perm` P.full_perm
  | _ -> true

[@@noextract_to "krml"] // proof-only
let scalar_mk_fraction
  (#t: Type)
  (x: scalar_t t)
  (p: P.perm)
: Pure (scalar_t t)
    (requires (scalar_fractionable x))
    (ensures (fun y -> p `P.lesser_equal_perm` P.full_perm ==> scalar_fractionable y))
= match x with
  | (Some (v, p')) ->
    (Some (v, p `prod_perm` p'))
  | _ -> x

#restart-solver
let scalar t = {
  pcm = F.pcm_frac;
  fractionable = scalar_fractionable #t;
  mk_fraction = scalar_mk_fraction #t;
  mk_fraction_full = (fun x ->
    match x with
    | (Some (v, p)) ->
      assert_norm ((P.full_perm `prod_perm` p).v == (let open FStar.Real in 1.0R *. p.v));
      assert (P.full_perm `prod_perm` p == p)
    | _ -> ()
  );
  mk_fraction_compose = (fun w p1 p2 ->
    match w with
    | (Some (v, p)) ->
      assert_norm (let open FStar.Real in ((p1 `prod_perm` p2) `prod_perm` p).v == (p1.v *. p2.v) *. p.v);
      assert_norm (let open FStar.Real in (p2 `prod_perm` (p1 `prod_perm` p)).v == p2.v *. (p1.v *. p.v));
      assert ((p1 `prod_perm` p2) `prod_perm` p == p2 `prod_perm` (p1 `prod_perm` p))
    | _ -> ()
  );
  fractionable_one = ();
  mk_fraction_one = (fun _ -> ());
  uninitialized = Some (None, P.full_perm);
  mk_fraction_split = (fun w p1 p2 ->
    match w with
    | (Some (v, p)) ->
      assert_norm (((p1 `P.sum_perm` p2) `prod_perm` p).v == (let open FStar.Real in (p1.v +. p2.v) *. p.v));
      assert_norm (((p1 `prod_perm` p) `P.sum_perm` (p2 `prod_perm` p)).v == (let open FStar.Real in (p1.v *. p.v) +. (p2.v *. p.v)));
      assert ((p1 `P.sum_perm` p2) `prod_perm` p == (p1 `prod_perm` p) `P.sum_perm` (p2 `prod_perm` p));
      assert (composable (F.pcm_frac) (scalar_mk_fraction w p1) (scalar_mk_fraction w p2));
()   //   assert (op (U.pcm_uninit F.pcm_frac) (scalar_mk_fraction w p1) (scalar_mk_fraction w p2) == scalar_mk_fraction w (p1 `P.sum_perm` p2))
    | _ -> ()
  );
  mk_fraction_join = (fun w p1 p2 ->
    match w with
    | (Some (v, p)) ->
      assert_norm (((p1 `P.sum_perm` p2) `prod_perm` p).v == (let open FStar.Real in (p1.v +. p2.v) *. p.v));
      assert_norm (((p1 `prod_perm` p) `P.sum_perm` (p2 `prod_perm` p)).v == (let open FStar.Real in (p1.v *. p.v) +. (p2.v *. p.v)));
      assert ((p1 `P.sum_perm` p2) `prod_perm` p == (p1 `prod_perm` p) `P.sum_perm` (p2 `prod_perm` p))
    | _ -> ()
  );
  mk_fraction_eq_one = (fun v p -> ());
}

let mk_scalar v = (Some (Some v, P.full_perm))

let mk_scalar_fractionable v p = ()

let mk_scalar_inj v1 v2 p1 p2 = ()

#push-options "--z3rlimit 16"

#restart-solver
let scalar_unique
  #_ #t v1 v2 p1 p2 r0
=
  let r : R.ref (scalar t).pcm = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 (mk_fraction (scalar _) (mk_scalar v1) p1))
    (R.pts_to r (Some (Some v1, p1)))
    (fun _ -> ());
  rewrite_slprop
    (pts_to r0 (mk_fraction (scalar _) (mk_scalar v2) p2))
    (R.pts_to r (Some (Some v2, p2)))
    (fun _ -> ());
  R.gather r (Some (Some v1, p1)) (Some (Some v2, p2));
  R.split r _ (Some (Some v1, p1)) (Some (Some v2, p2));
  rewrite_slprop
    (R.pts_to r (Some (Some v1, p1)))
    (pts_to r0 (mk_fraction (scalar _) (mk_scalar v1) p1))
    (fun _ -> ());
  rewrite_slprop
    (R.pts_to r (Some (Some v2, p2)))
    (pts_to r0 (mk_fraction (scalar _) (mk_scalar v2) p2))
    (fun _ -> ())

#pop-options

let read0
  #t #v #p r0
=
  let r : R.ref (scalar t).pcm = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
    (R.pts_to r (Some (Some (Ghost.reveal v), p)))
    (fun _ -> ());
  let v' = R.ref_read r in
  rewrite_slprop
    (R.pts_to r (Some (Some (Ghost.reveal v), p)))
    (pts_to r0 (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
    (fun _ -> ());
  let Some (Some v0, _) = v' in
  return v0

let write
  #t #v r0 v'
=
  let r : R.ref (scalar t).pcm = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 v)
    (R.pts_to r v)
    (fun _ -> ());
  R.ref_upd r _ _ (R.base_fpu _ _ (Some (Some v', P.full_perm)));
  rewrite_slprop
    (R.pts_to r _)
    (pts_to _ _)
    (fun _ -> ())

let field_t_nil = unit
let field_t_cons _ _ _ = unit

irreducible let norm_field_attr = ()

let define_struct0 _ _ _ = unit

[@@noextract_to "krml"]
noeq
type field_description_gen_t (field_t: eqtype) : Type u#1 = {
  fd_nonempty: squash (exists (f: field_t) . True);
  fd_type: (field_t -> Type0);
  fd_typedef: ((s: field_t) -> Tot (typedef (fd_type s)));
}

let nonempty_field_description_nonempty
  (#tf: Type)
  (fd: nonempty_field_description_t tf)
: Lemma
  (exists (f: field_t fd) . True)
= if StrongExcludedMiddle.strong_excluded_middle (exists (f: field_t fd) . True)
  then ()
  else begin
    let prf
      (f: string)
    : Lemma
      (fd.fd_def f == false)
    = if fd.fd_def f
      then Classical.exists_intro (fun (f: field_t fd) -> True) f
      else ()
    in
    Classical.forall_intro prf
  end

[@@noextract_to "krml"]
let fd_gen_of_nonempty_fd (#tf: Type0) (fd: nonempty_field_description_t tf) : Tot (field_description_gen_t (field_t fd)) = {
  fd_nonempty = nonempty_field_description_nonempty fd;
  fd_type = fd.fd_type;
  fd_typedef = (fun (s: field_t fd) -> fd.fd_typedef s);
}

module S = Steel.C.Model.Struct

[@@noextract_to "krml"] // proof-only
let struct_field_pcm
  (#field_t: eqtype)
  (fields: field_description_gen_t field_t)
  (f: field_t)
: Tot (pcm (fields.fd_type f))
= (fields.fd_typedef f).pcm

module FX = FStar.FunctionalExtensionality

[@@noextract_to "krml"] // primitive
let struct_t1 (#field_t: eqtype) (fields: field_description_gen_t field_t) : Tot Type0 =
  FX.restricted_t field_t fields.fd_type

let struct_t0 _ n fields =
  struct_t1 (fd_gen_of_nonempty_fd fields)

[@@noextract_to "krml"] // proof-only
let struct_pcm
  (#field_t: eqtype)
  (fields: field_description_gen_t field_t)
: Tot (pcm (struct_t1 fields))
= S.prod_pcm (struct_field_pcm fields)

[@@noextract_to "krml"] // proof-only
let t_struct_set_field
  (#field_t: eqtype) (#fields: field_description_gen_t field_t) (f: field_t) (v: fields.fd_type f) (s: struct_t1 fields)
: Tot (struct_t1 fields)
= FX.on_dom (field_t) (fun f' -> if f = f' then v else s f')

let struct_set_field
  f v s
= t_struct_set_field f v s

let struct_get_field
  s field
= s field

let struct_eq
  s1 s2
= s1 `FX.feq` s2

let struct_eq_intro
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (s1 s2: struct_t1 fields)
  (prf: (
    (f: field_t) ->
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
  (#field_t: eqtype) (#fields: field_description_gen_t field_t)
  (s: struct_t1 fields)
: GTot bool
= FStar.StrongExcludedMiddle.strong_excluded_middle (forall (f: field_t) . (fields.fd_typedef f).fractionable (s f))

[@@noextract_to "krml"] // proof-only
let struct_mk_fraction
  (#field_t: eqtype) (#fields: field_description_gen_t field_t)
  (s: struct_t1 fields)
  (p: P.perm)
: Pure (struct_t1 fields)
  (requires (struct_fractionable s))
  (ensures (fun s' -> p `P.lesser_equal_perm` P.full_perm ==> struct_fractionable s'))
= FX.on_dom field_t (fun f -> (fields.fd_typedef f).mk_fraction (s f) p)

[@@noextract_to "krml"] // proof-only
let struct_uninitialized
  (#field_t: eqtype) (fields: field_description_gen_t field_t)
: Pure (struct_t1 fields)
    (requires True)
    (ensures (fun y -> p_refine (struct_pcm fields) y))
= FX.on_dom field_t (fun f -> (fields.fd_typedef f).uninitialized <: fields.fd_type f)

let struct1
  (#field_t: eqtype)
  (fields: field_description_gen_t field_t)
= {
  pcm = struct_pcm fields;
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
    struct_eq_intro (struct_mk_fraction (one (struct_pcm fields)) p) (one (struct_pcm fields)) (fun f ->
      (fields.fd_typedef f).mk_fraction_one p
    )
  );
  uninitialized = struct_uninitialized _;
  mk_fraction_split = (fun v p1 p2 ->
    let prf
      (f: field_t)
    : Lemma
      (composable (fields.fd_typedef f).pcm (mk_fraction (fields.fd_typedef f) (v f) p1) (mk_fraction (fields.fd_typedef f) (v f) p2))
    = (fields.fd_typedef f).mk_fraction_split (v f) p1 p2
    in
    Classical.forall_intro prf
  );
  mk_fraction_join = (fun v p1 p2 ->
    struct_eq_intro (op (struct_pcm fields) (struct_mk_fraction v p1) (struct_mk_fraction v p2)) (struct_mk_fraction v (p1 `P.sum_perm` p2)) (fun f ->
      (fields.fd_typedef f).mk_fraction_join (v f) p1 p2
    )
  );
  mk_fraction_eq_one = (fun v p ->
    struct_eq_intro v (one (struct_pcm fields)) (fun f ->
      (fields.fd_typedef f).mk_fraction_eq_one (v f) p
    )
  );
}

let struct0 _ _ _ = struct1 _

let struct_get_field_unknown
  tn n fields field
= ()

let struct_get_field_uninitialized
  tn n fields field
= ()

let _inv = TD.inv

let has_struct_field_gen
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (r: ref (struct1 fields))
  (field: field_t)
  (r': ref (fields.fd_typedef field))
: GTot prop
= (Some?.v r').ref == R.ref_focus (Some?.v r).ref (S.struct_field (struct_field_pcm fields) field)

let has_struct_field
  r field r'
= has_struct_field_gen r field r'

let has_struct_field_gen_inj
  (#opened: _)
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (r: ref (struct1 fields))
  (field: field_t)
  (r1 r2: ref (fields.fd_typedef field))
: SteelGhost unit opened
    emp
    (fun _ -> emp)
    (fun _ ->
      Ghost.reveal (mem_inv opened _inv) == false /\
      has_struct_field_gen r field r1 /\
      has_struct_field_gen r field r2
    )
    (fun _ _ _ -> r1 == r2)
= TD.type_of_token_inj (Some?.v r1).dest (Some?.v r2).dest

let has_struct_field_inj
  r field r1 r2
= has_struct_field_gen_inj r field r1 r2

#push-options "--z3rlimit 32"

#restart-solver

let ghost_struct_field_focus
  #_ #tn #_ #n #fields #v r0 field r'0
= let r : R.ref (struct_pcm _) = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 v)
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
  let vf = S.field_to_struct_f (struct_field_pcm _) field (struct_get_field v field) in
  assert (composable (struct_pcm _) v' vf);
  assert (op (struct_pcm _) v' vf `FX.feq` v);
  R.split r _ v' vf;
  R.gfocus r (S.struct_field (struct_field_pcm _) field) vf (struct_get_field v field);
  rewrite_slprop
    (R.pts_to r _)
    (pts_to r0 _)
    (fun _ -> ());
  rewrite_slprop
    (R.pts_to _ _)
    (pts_to r'0 _)
    (fun _ -> ())

let ghost_struct_field
  #_ #tn #_ #n #fields #v r field
= let tok' = TD.get_token (fields.fd_type field) in
  let r' : ref (fields.fd_typedef field) = Some ({
    dest = tok';
    typedef = fields.fd_typedef field;
    ref = R.ref_focus (Some?.v r).ref (S.struct_field (struct_field_pcm (fd_gen_of_nonempty_fd fields)) field);
  })
  in
  let gr' = Ghost.hide r' in
  ghost_struct_field_focus r field gr';
  gr'

[@@noextract_to "krml"] // primitive
let struct_field'
  (#tn: Type0)
  (#tf: Type0)
  (#opened: _)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r0: ref (struct0 tn n fields))
  (field: field_t fields)
: SteelAtomicBase (ref (fields.fd_typedef field)) false opened Unobservable
    (pts_to r0 v)
    (fun r' -> pts_to r0 (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (struct_get_field v field))
    (fun _ -> Ghost.reveal (mem_inv opened _inv) == false)
    (fun _ r' _ -> has_struct_field r0 field r')
= let r : R.ref (struct_pcm _) = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 v)
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
  let vf = Ghost.hide (S.field_to_struct_f (struct_field_pcm _) field (struct_get_field v field)) in
  assert (composable (struct_pcm _) v' vf);
  assert (op (struct_pcm _) v' vf `FX.feq` v);
  R.split r _ v' vf;
  let r' = R.focus r (S.struct_field (struct_field_pcm _) field) vf (struct_get_field v field) in
  let tok' = TD.get_token (fields.fd_type field) in
  let res : ref (fields.fd_typedef field) = Some ({
    dest = tok';
    typedef = fields.fd_typedef field;
    ref = r';
  })
  in
  rewrite_slprop
    (R.pts_to r _)
    (pts_to r0 _)
    (fun _ -> ());
  rewrite_slprop
    (R.pts_to _ _)
    (pts_to res _)
    (fun _ -> ());
  return res

let struct_field0
  t' r field td'
=
  let r' = struct_field' r field in
  let res : ref td' = r' in
  change_equal_slprop (pts_to r' _) (pts_to res _);
  return res

let unstruct_field
  #_ #tn #_ #n #fields #v r0 field #v' r'0
= let r : R.ref (struct_pcm _) = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 v)
    (R.pts_to r v)
    (fun _ -> ());
  let r' : R.ref (fields.fd_typedef field).pcm = (Some?.v r'0).ref in
  rewrite_slprop
    (pts_to r'0 v')
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
  let vf = S.field_to_struct_f (struct_field_pcm _) field v' in
  assert (composable (struct_pcm _) v vf);
  assert (op (struct_pcm _) v vf `FX.feq` struct_set_field field v' v);
  R.unfocus r' r (S.struct_field (struct_field_pcm _) field) _;
  R.gather r v _;
  rewrite_slprop
    (R.pts_to r _)
    (pts_to r0 _)
    (fun _ -> ())

#pop-options

let fractionable_struct _ = ()
let mk_fraction_struct _ _ _ = ()

let full_struct_gen
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (s: struct_t1 fields)
: Lemma
  (full (struct1 fields) s <==> (forall field . full (fields.fd_typedef field) (s field)))
=
  let is_unit'
    (f': field_t)
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
    (field: field_t)
  : Lemma
    (requires (full (struct1 fields) s))
    (ensures (full (fields.fd_typedef field) (s field)))
  = let prf'
      (x: fields.fd_type field)
    : Lemma
      (requires (composable (fields.fd_typedef field).pcm (s field) x))
      (ensures (x == one (fields.fd_typedef field).pcm))
    = let s' = t_struct_set_field field x (one (struct_pcm fields)) in
      assert (composable (struct_pcm fields) s s')
    in
    Classical.forall_intro (Classical.move_requires prf')
  in
  Classical.forall_intro (Classical.move_requires prf)

let full_struct s = full_struct_gen s

module U = Steel.C.Model.Union

let define_union0 _ _ _ = unit

[@@noextract_to "krml"] // proof-only
let union_field_t
  (#t: Type)
  (fd: field_description_t t)
: Tot Type0
= option (field_t fd)

[@@noextract_to "krml"] // proof-only
let union_field_type
  (#t: Type)
  (fd: field_description_t t)
  (field: union_field_t fd)
: Tot Type0
= match field with
  | None -> scalar_t unit
  | Some f -> fd.fd_type f

[@@noextract_to "krml"] // proof-only
let union_field_typedef
  (#t: Type)
  (fd: field_description_t t)
  (field: union_field_t fd)
: Tot (typedef (union_field_type fd field))
= match field with
  | None -> scalar unit
  | Some f -> fd.fd_typedef f

[@@noextract_to "krml"] // proof-only
let union_field_pcm
  (#t: Type)
  (fd: field_description_t t)
  (field: union_field_t fd)
: Tot (pcm (union_field_type fd field))
= (union_field_typedef fd field).pcm

let union_t0
  tn n fields
= U.union (union_field_pcm fields)

let union_set_field
  tn n fields f v
= U.field_to_union_f (union_field_pcm fields) (Some f) v

let union_get_case
  u
= match U.case_of_union _ u with
  | None -> None
  | Some s -> s

let union_get_field
  u field
= U.union_to_field_f _ (Some field) u

let union_get_field_same
  tn n fields field v
= ()

let union_set_field_same
  #tn #_ #n #fields  s field
= assert (union_set_field tn n fields field (union_get_field s field) `FX.feq` s)

let union_fractionable
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: field_description_t tf)
  (s: union_t0 tn n fields)
: GTot bool
= match U.case_of_union (union_field_pcm fields) s with
  | Some f -> (union_field_typedef fields f).fractionable (s f)
  | _ -> true

let union_fractionable_fields
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: field_description_t tf)
  (s: union_t0 tn n fields)
  (f: union_field_t fields)
: Lemma
  (requires (union_fractionable s))
  (ensures (fractionable (union_field_typedef fields f) (s f)))
= ()

[@@noextract_to "krml"] // proof-only
let union_mk_fraction
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: field_description_t tf)
  (s: union_t0 tn n fields)
  (p: P.perm)
: Pure (union_t0 tn n fields)
  (requires (union_fractionable s))
  (ensures (fun s' -> p `P.lesser_equal_perm` P.full_perm ==> union_fractionable s'))
= let prf
    (f: union_field_t fields)
  : Lemma
    (let u = one (union_field_typedef fields f).pcm in
      (union_field_typedef fields f).mk_fraction u p == u
    )
  = (union_field_typedef fields f).mk_fraction_one p
  in
  Classical.forall_intro prf;
  FX.on_dom (union_field_t fields) (fun f ->
    (union_field_typedef fields f).mk_fraction (s f) p
  )

[@@noextract_to "krml"] // proof-only
let union_pcm
  (tn: Type0) (#tf: Type0) (n: string) (fields: field_description_t tf)
: Tot (pcm (union_t0 tn n fields))
= U.union_pcm (union_field_pcm fields)

let union_eq_intro
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s1 s2: union_t0 tn n fields)
  (prf: (
    (f: union_field_t fields) ->
    Lemma
    (s1 f == s2 f)
  ))
: Lemma
  (s1 == s2)
= Classical.forall_intro prf;
  assert (s1 `FX.feq` s2)

[@@noextract_to "krml"] // proof-only
let union_uninitialized
  (tn: Type0) (#tf: Type0) (n: string) (fields: field_description_t tf)
: Pure (union_t0 tn n fields)
  (requires True)
  (ensures (fun y -> exclusive (union_pcm tn n fields) y /\ p_refine (union_pcm tn n fields) y))
= let y : union_t0 tn n fields =
    U.field_to_union_f (union_field_pcm fields) None (scalar unit).uninitialized
  in
  U.exclusive_union_intro (union_field_pcm fields) y None;
  y

#push-options "--z3rlimit 16"

#restart-solver
let union0
  tn n fields
= {
  pcm = union_pcm tn n fields;
  fractionable = union_fractionable;
  mk_fraction = union_mk_fraction;
  mk_fraction_full = (fun x ->
    union_eq_intro (union_mk_fraction x P.full_perm) x (fun f ->
      (union_field_typedef fields f).mk_fraction_full (x f)
    )
  );
  mk_fraction_compose = (fun x p1 p2 ->
    union_eq_intro (union_mk_fraction (union_mk_fraction x p1) p2) (union_mk_fraction x (p1 `prod_perm` p2)) (fun f ->
      union_fractionable_fields x f;
      (union_field_typedef fields f).mk_fraction_compose (x f) p1 p2
    )
  );
  fractionable_one = ();
  mk_fraction_one = (fun p ->
    union_eq_intro (union_mk_fraction (one (union_pcm tn n fields)) p) (one (union_pcm tn n fields)) (fun f ->
      (union_field_typedef fields f).mk_fraction_one p
    )
  );
  uninitialized = union_uninitialized _ _ _;
  mk_fraction_split = (fun v p1 p2 ->
    U.union_comp_intro (union_field_pcm fields) (union_mk_fraction v p1) (union_mk_fraction v p2) (fun j k ->
      (union_field_typedef fields j).mk_fraction_one p1;
      (union_field_typedef fields k).mk_fraction_one p2;
      assert (j == k);
      (union_field_typedef fields j).mk_fraction_split (v j) p1 p2
    )
  );
  mk_fraction_join = (fun v p1 p2 ->
    union_eq_intro (op (union_pcm tn n fields) (union_mk_fraction v p1) (union_mk_fraction v p2)) (union_mk_fraction v (p1 `P.sum_perm` p2)) (fun f ->
      (union_field_typedef fields f).mk_fraction_join (v f) p1 p2
    )
  );
  mk_fraction_eq_one = (fun v p ->
    union_eq_intro v (one (union_pcm tn n fields)) (fun f ->
      (union_field_typedef fields f).mk_fraction_eq_one (v f) p
    )
  );
}

#pop-options

let union_get_case_unknown
  tn n fields
= ()

let union_set_field_unknown
  tn n fields field
= ()

let union_get_case_uninitialized
  tn n fields
= ()

let mk_fraction_union_get_case
  #tn #_ #n #fields s p
= match U.case_of_union (union_field_pcm fields) s with
  | None -> (union0 tn n fields).mk_fraction_one p
  | Some f ->
    Classical.move_requires ((union_field_typedef fields f).mk_fraction_eq_one (s f)) p

let fractionable_union_get_field
  s field
= ()

let mk_fraction_union_get_field
  s p field
= ()

let mk_fraction_union_set_field
  tn n fields field v p
= 
  assert (fractionable (union0 tn n fields) (union_set_field tn n fields field v));
  let prf
    (f: union_field_t fields)
  : Lemma
    (let u = one (union_field_typedef fields f).pcm in
      (union_field_typedef fields f).mk_fraction u p == u
    )
  = (union_field_typedef fields f).mk_fraction_one p
  in
  Classical.forall_intro prf;
  assert (mk_fraction (union0 tn n fields) (union_set_field tn n fields field v) p `FX.feq` union_set_field tn n fields field (mk_fraction (fields.fd_typedef field) v p))

let full_union
  #_ #_ #_ #fields s field
= Classical.move_requires (U.exclusive_union_intro (union_field_pcm fields) s) (Some field);
  Classical.move_requires (U.exclusive_union_elim (union_field_pcm fields) s) (Some field) 

let has_union_field
  #_ #_ #_ #fields r field r'
= (Some?.v r').ref == R.ref_focus (Some?.v r).ref (U.union_field (union_field_pcm fields) (Some field))

let has_union_field_inj
  #_ #_ #_ #fields r field r1 r2
= TD.type_of_token_inj (Some?.v r1).dest (Some?.v r2).dest

#push-options "--z3rlimit 16"

#restart-solver
let ghost_union_field_focus
  #_ #tn #_ #n #fields #v r0 field r'0
= let r : R.ref (union_pcm tn n fields) = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 v)
    (R.pts_to r v)
    (fun _ -> ());
  let v' = U.field_to_union_f (union_field_pcm fields) (Some field) (union_get_field v field) in
  assert (v' `FX.feq` v);
  R.gfocus r (U.union_field (union_field_pcm fields) (Some field)) v (union_get_field v field);
  rewrite_slprop
    (R.pts_to _ _)
    (pts_to r'0 _)
    (fun _ -> ())

let ghost_union_field
  #_ #tn #_ #n #fields #v r field
= let tok' = TD.get_token (fields.fd_type field) in
  let r' : ref (fields.fd_typedef field) = Some ({
    dest = tok';
    typedef = fields.fd_typedef field;
    ref = R.ref_focus (Some?.v r).ref (U.union_field (union_field_pcm fields) (Some field));
  })
  in
  let gr' = Ghost.hide r' in
  ghost_union_field_focus r field gr';
  gr'

[@@noextract_to "krml"] // primitive
let union_field'
  (#tn: Type0)
  (#tf: Type0)
  (#opened: _)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r0: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
: SteelAtomicBase (ref (fields.fd_typedef field)) false opened Unobservable
    (pts_to r0 v)
    (fun r' -> pts_to r' (union_get_field v field))
    (fun _ -> Ghost.reveal (mem_inv opened _inv) == false)
    (fun _ r' _ -> has_union_field r0 field r')
= let r : R.ref (union_pcm tn n fields) = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 v)
    (R.pts_to r v)
    (fun _ -> ());
  let v' = Ghost.hide (U.field_to_union_f (union_field_pcm fields) (Some field) (union_get_field v field)) in
  assert (v' `FX.feq` v);
  let r' = R.focus r (U.union_field (union_field_pcm fields) (Some field)) v (union_get_field v field) in
  let tok' = TD.get_token (fields.fd_type field) in
  let res : ref (fields.fd_typedef field) = Some ({
    dest = tok';
    typedef = fields.fd_typedef field;
    ref = r';
  })
  in
  rewrite_slprop
    (R.pts_to _ _)
    (pts_to res _)
    (fun _ -> ());
  return res

let union_field0
  t' r field td'
=
  let r' = union_field' r field in
  let res : ref td' = r' in
  change_equal_slprop (pts_to r' _) (pts_to res _);
  return res

let ununion_field
  #_ #tn #_ #n #fields r0 field #v' r'0
= let r : R.ref (union_pcm tn n fields) = (Some?.v r0).ref in
  let r' : R.ref (fields.fd_typedef field).pcm = (Some?.v r'0).ref in
  rewrite_slprop
    (pts_to r'0 v')
    (R.pts_to r' v')
    (fun _ -> ());
  R.unfocus r' r (U.union_field (union_field_pcm fields) (Some field)) _;
  rewrite_slprop
    (R.pts_to r _)
    (pts_to r0 _)
    (fun _ -> ())

[@@noextract_to "krml"] // primitive
let union_switch_field'
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r0: ref (union0 tn n fields))
  (field: field_t fields)
: Steel (ref (fields.fd_typedef field))
    (pts_to r0 v)
    (fun r' -> pts_to #(norm norm_field_steps (fields.fd_type field)) r' (uninitialized (fields.fd_typedef field)))
    (fun _ -> full (union0 tn n fields) v)
    (fun _ r' _ -> has_union_field r0 field r')
= let r : R.ref (union_pcm tn n fields) = (Some?.v r0).ref in
  rewrite_slprop
    (pts_to r0 v)
    (R.pts_to r v)
    (fun _ -> ());
  let v' = U.field_to_union_f (union_field_pcm fields) (Some field) (fields.fd_typedef field).uninitialized in
  R.ref_upd r _ _ (R.base_fpu (union_pcm tn n fields) _ v');
  rewrite_slprop
    (R.pts_to _ _)
    (pts_to r0 v')
    (fun _ -> ());
  let r' = union_field' r0 field in
  return r'

let union_switch_field0
  t' r field td'
=
  let r' = union_switch_field' r field in
  let res : ref td' = r' in
  change_equal_slprop (pts_to r' _) (pts_to res _);
  return res

#pop-options
