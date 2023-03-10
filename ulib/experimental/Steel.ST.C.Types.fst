module Steel.ST.C.Types
open Steel.C.Model.PCM
open Steel.ST.GenElim

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

module R = Steel.ST.C.Model.Ref

noeq
type ref0_v (#t: Type) (td: typedef t) : Type u#1 = {
  base: Type0;
  ref: R.ref base td.pcm;
}

module HR = Steel.ST.HigherReference

let ptr #t td = HR.ref (ref0_v td)
let null td = HR.null

(*
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
*)

let r_pts_to
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: R.ref a p) (v: b)
: vprop
= R.pts_to r v

[@@__reduce__]
let pts_to0
  (#t: Type)
  (#td: typedef t)
  (r: ptr td)
  (v: t)
: Tot vprop
= exists_ (fun p -> exists_ (fun w ->
    HR.pts_to r p w `star`
    r_pts_to w.ref v
  ))

let pts_to r v = pts_to0 r v

let pts_to_intro
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (p: P.perm)
  (w1 w2: ref0_v td)
  (v: t)
: STGhost unit opened
    (HR.pts_to r p w1 `star` R.pts_to w2.ref v)
    (fun _ -> pts_to r v)
    (w1 == w2)
    (fun _ -> True)
= vpattern_rewrite (HR.pts_to r p) w2;
  rewrite (pts_to0 r v) (pts_to r v)

let is_null
  p
= let res = HR.is_null p in
  return res

[@@__reduce__]
let ref_equiv0
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: Tot vprop
= exists_ (fun p1 -> exists_ (fun p2 -> exists_ (fun w ->
    HR.pts_to r1 p1 w `star`
    HR.pts_to r2 p2 w
  )))

let ref_equiv
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: Tot vprop
= ref_equiv0 r1 r2

let ref_equiv_dup'
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: STGhostT unit opened
    (ref_equiv r1 r2)
    (fun _ -> ref_equiv r1 r2 `star` ref_equiv r1 r2)
= rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = gen_elim () in
  HR.share r1;
  HR.share r2;
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2);
  noop ();
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let ref_equiv_sym'
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: STGhostT unit opened
    (ref_equiv r1 r2)
    (fun _ -> ref_equiv r1 r2 `star` ref_equiv r2 r1)
= ref_equiv_dup' r1 r2;
  rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = gen_elim () in
  noop ();
  rewrite (ref_equiv0 r2 r1) (ref_equiv r2 r1)

let hr_share (#a:Type)
          (#uses:_)
          (#p:P.perm)
          (#v:a)
          (r:HR.ref a)
  : STGhostT unit uses
      (HR.pts_to r p v)
      (fun _ -> HR.pts_to r (P.half_perm p) v `star` HR.pts_to r (P.half_perm p) v)
= HR.share #_ #_ #_ #v r

let hr_gather
  (#a:Type)
  (#uses:_) 
  (#p0 #p1:P.perm)
  (v0 #v1:a)
  (r:HR.ref a)
: STGhost unit uses
      (HR.pts_to r p0 v0 `star` HR.pts_to r p1 v1)
      (fun _ -> HR.pts_to r (P.sum_perm p0 p1) v0)
      (requires True)
      (ensures fun _ -> v0 == v1)
= HR.gather p1 r

let ref_equiv_trans'
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r1 r2 r3: ref td)
: STGhostT unit opened
    (ref_equiv r1 r2 `star` ref_equiv r2 r3)
    (fun _ -> ref_equiv r1 r2 `star` ref_equiv r2 r3 `star` ref_equiv r1 r3)
= rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = gen_elim () in
  let w = vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  let p2 = vpattern_replace (fun p -> HR.pts_to r2 p _) in
  rewrite (ref_equiv r2 r3) (ref_equiv0 r2 r3);
  let _ = gen_elim () in
  HR.pts_to_injective_eq #_ #_ #_ #_ #w #_ r2;
  vpattern_rewrite (HR.pts_to r3 _) w;
  hr_share r1;
  hr_share r3;
  HR.gather p2 r2;
  hr_share r2;
  noop ();
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2);
  rewrite (ref_equiv0 r2 r3) (ref_equiv r2 r3);
  rewrite (ref_equiv0 r1 r3) (ref_equiv r1 r3)

let hr_share_imbalance (#a:Type)
          (#uses:_)
          (#p:P.perm)
          (#v:a)
          (r:HR.ref a)
  : STGhostT P.perm uses
      (HR.pts_to r p v)
      (fun p1 -> HR.pts_to r p1 v `star` exists_ (fun p2 -> HR.pts_to r p2 v))
= HR.share #_ #_ #_ #v r;
  _

#set-options "--ide_id_info_off"

let pts_to_equiv
  r1 r2 v
= rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = gen_elim () in
  let w = vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  rewrite (pts_to r1 v) (pts_to0 r1 v);
  let _ = gen_elim () in
  hr_gather w r1;
  hr_share r2;
  rewrite (R.pts_to _ _) (R.pts_to w.ref v);
  rewrite (pts_to0 r2 v) (pts_to r2 v);
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

[@@__steel_reduce__; __reduce__]
let freeable0
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
: Tot vprop
= exists_ (fun p -> exists_ (fun w ->
    HR.pts_to r p w `star`
    pure (R.freeable w.ref)
  ))

let freeable
  r
= freeable0 r

let freeable_dup
  r
= rewrite (freeable r) (freeable0 r);
  let _ = gen_elim () in
  HR.share r;
  noop ();
  rewrite (freeable0 r) (freeable r);
  noop ();
  rewrite (freeable0 r) (freeable r)

let freeable_equiv
  r1 r2
= rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = gen_elim () in
  let w = vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  rewrite (freeable r1) (freeable0 r1);
  let _ = gen_elim () in
  hr_gather w r1;
  HR.share r2;
  rewrite (freeable0 r2) (freeable r2);
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let alloc
  td
= let r = R.ref_alloc td.pcm td.uninitialized in
  let w = {
    base = _;
    ref = r;
  }
  in
  rewrite (R.pts_to _ _) (R.pts_to w.ref (uninitialized td));
  let res = HR.alloc w in
  HR.share res;
  HR.pts_to_not_null res;
  rewrite (pts_to0 res (uninitialized td)) (pts_to_or_null res (uninitialized td));
  rewrite (freeable0 res) (freeable_or_null res);
  return res

let free
  #_ #_ #v r
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = HR.read r in
  rewrite (R.pts_to _ _) (R.pts_to w.ref v);
  rewrite (freeable r) (freeable0 r);
  let _ = gen_elim () in
  hr_gather w r;
  R.ref_free w.ref;
  drop (HR.pts_to _ _ _);
  return ()

let mk_fraction_split_gen
  #_ #_ #td r v p p1 p2
= rewrite (pts_to _ _) (pts_to0 r (mk_fraction td v p));
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  td.mk_fraction_split v p1 p2;
  td.mk_fraction_join v p1 p2;
  rewrite
    (R.pts_to _ _)
    (R.pts_to w.ref (op td.pcm (td.mk_fraction v p1) (td.mk_fraction v p2)));
  R.split _ _ (td.mk_fraction v p1) (td.mk_fraction v p2);
  HR.share r;
  rewrite (pts_to0 r (td.mk_fraction v p1)) (pts_to r (mk_fraction td v p1));
  rewrite (pts_to0 r (td.mk_fraction v p2)) (pts_to r (mk_fraction td v p2))

let mk_fraction_join
  #_ #_ #td r v p1 p2
= rewrite (pts_to r (mk_fraction td v p1)) (pts_to0 r (mk_fraction td v p1));
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  rewrite (R.pts_to _ _) (R.pts_to w.ref (td.mk_fraction v p1));
  rewrite (pts_to r (mk_fraction td v p2)) (pts_to0 r (mk_fraction td v p2));
  let _ = gen_elim () in
  hr_gather w r;
  rewrite (R.pts_to _ (mk_fraction _ _ p2)) (R.pts_to w.ref (td.mk_fraction v p2));
  let _ = R.gather w.ref (td.mk_fraction v p1) _ in
  td.mk_fraction_join v p1 p2;
  rewrite (pts_to0 r _) (pts_to r _)

module F = Steel.ST.C.Model.Frac

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
  #_ #t v1 v2 p1 p2 r
= rewrite (pts_to r (mk_fraction (scalar t) (mk_scalar v1) p1)) (pts_to0 r (Some (Some v1, p1)));
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  rewrite (r_pts_to _ (Some (Some v1, p1))) (R.pts_to w.ref (Some (Some v1, p1)));
  rewrite (pts_to r _) (pts_to0 r (Some (Some v2, p2)));
  let _ = gen_elim () in
  hr_gather w r;
  rewrite (r_pts_to _ (Some (Some v2, p2))) (R.pts_to w.ref (Some (Some v2, p2)));
  let _ = R.gather w.ref (Some (Some v1, p1)) (Some (Some v2, p2)) in
  R.split w.ref _ (Some (Some v1, p1)) (Some (Some v2, p2));
  HR.share r;
  noop (); // FIXME: WHY WHY WHY?
  rewrite (pts_to0 r (Some (Some v1, p1))) (pts_to r (mk_fraction (scalar _) (mk_scalar v1) p1));
  rewrite (pts_to0 r (Some (Some v2, p2))) (pts_to r (mk_fraction (scalar _) (mk_scalar v2) p2))

#pop-options

let read0
  #t #v #p r
= rewrite (pts_to r _) (pts_to0 r (Some (Some (Ghost.reveal v), p)));
  let _ = gen_elim () in
  let w = HR.read r in
  vpattern_rewrite (HR.pts_to r _) w;
  rewrite (r_pts_to _ _) (R.pts_to w.ref (Some (Some (Ghost.reveal v), p)));
  let v' = R.ref_read w.ref in
  let Some (Some v0, _) = v' in
  rewrite (R.pts_to _ _) (r_pts_to w.ref (Some (Some (Ghost.reveal v), p)));
  rewrite (pts_to0 r (Some (Some (Ghost.reveal v), p))) (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p));
  return v0

let write
  #t #v r v'
= rewrite (pts_to r _) (pts_to0 r (Ghost.reveal v));
  let _ = gen_elim () in
  let w = HR.read r in
  vpattern_rewrite (HR.pts_to r _) w;
  rewrite (r_pts_to _ _) (R.pts_to w.ref (Ghost.reveal v));
  R.ref_upd w.ref _ _ (R.base_fpu _ _ (Some (Some v', P.full_perm)));
  rewrite (R.pts_to _ _) (r_pts_to w.ref (Some (Some (Ghost.reveal v'), P.full_perm)));
  rewrite (pts_to0 r (Some (Some (Ghost.reveal v'), P.full_perm))) (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v')) P.full_perm))

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

module S = Steel.ST.C.Model.Struct

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

[@@noextract_to "krml"] // proof-only
let t_struct_get_field
  (#field_t: eqtype) (#fields: field_description_gen_t field_t) (s: struct_t1 fields) (f: field_t)
: Tot (fields.fd_type f)
= s f

let struct_get_field
  s field
= t_struct_get_field s field

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

let has_struct_field_gen
  (#field_t: eqtype)
  (fields: field_description_gen_t field_t)
  (r: ref0_v (struct1 fields))
  (field: field_t)
  (r': ref0_v (fields.fd_typedef field))
: GTot prop
= r'.base == r.base /\
  r'.ref == R.ref_focus r.ref (S.struct_field (struct_field_pcm fields) field)

[@@__reduce__]
let has_struct_field0
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (r: ref (struct1 fields))
  (field: field_t)
  (r': ref (fields.fd_typedef field))
: Tot vprop
= exists_ (fun p -> exists_ (fun w -> exists_ (fun p' -> exists_ (fun w' ->
    HR.pts_to r p w `star`
    HR.pts_to r' p' w' `star`
    pure (has_struct_field_gen fields w field w')
  ))))

let has_struct_field1
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (r: ref (struct1 fields))
  (field: field_t)
  (r': ref (fields.fd_typedef field))
: Tot vprop
= has_struct_field0 r field r'

let has_struct_field
  r field r'
= has_struct_field1 r field r'

let has_struct_field_dup'
  (#opened: _)
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (r: ref (struct1 fields))
  (field: field_t)
  (r': ref (fields.fd_typedef field))
: STGhostT unit opened
    (has_struct_field1 r field r')
    (fun _ -> has_struct_field1 r field r' `star` has_struct_field1 r field r')
=
  rewrite (has_struct_field1 r field r') (has_struct_field0 r field r');
  let _ = gen_elim () in
  HR.share r;
  HR.share r';
  noop ();
  rewrite (has_struct_field0 r field r') (has_struct_field1 r field r');
  noop ();
  rewrite (has_struct_field0 r field r') (has_struct_field1 r field r')

let has_struct_field_dup
  r field r'
= has_struct_field_dup' r field r'

let has_struct_field_inj'
  (#opened: _)
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (r: ref (struct1 fields))
  (field: field_t)
  (r1 r2: ref (fields.fd_typedef field))
: STGhostT unit opened
    (has_struct_field1 r field r1 `star` has_struct_field1 r field r2)
    (fun _ -> has_struct_field1 r field r1 `star` has_struct_field1 r field r2 `star` ref_equiv r1 r2)
=
  rewrite (has_struct_field1 r field r1) (has_struct_field0 r field r1);
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let w1 = vpattern_replace (HR.pts_to r1 _) in
  rewrite (has_struct_field1 r field r2) (has_struct_field0 r field r2);
  let _ = gen_elim () in
  hr_gather w r;
  vpattern_rewrite (HR.pts_to r2 _) w1;
  hr_share r;
  hr_share r1;
  rewrite (has_struct_field0 r field r1) (has_struct_field1 r field r1);
  hr_share r2;
  rewrite (has_struct_field0 r field r2) (has_struct_field1 r field r2);
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let has_struct_field_inj
  r field r1 r2
= has_struct_field_inj' r field r1 r2

let has_struct_field_equiv_from'
  (#opened: _)
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (r1: ref (struct1 fields))
  (field: field_t)
  (r': ref (fields.fd_typedef field))
  (r2: ref (struct1 fields))
: STGhostT unit opened
    (ref_equiv r1 r2 `star` has_struct_field1 r1 field r')
    (fun _ -> ref_equiv r1 r2 `star` has_struct_field1 r2 field r')
= rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = gen_elim () in
  let w = vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  rewrite (has_struct_field1 r1 field r') (has_struct_field0 r1 field r');
  let _ = gen_elim () in
  hr_gather w r1;
  hr_share r2;
  rewrite (has_struct_field0 r2 field r') (has_struct_field1 r2 field r');
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let has_struct_field_equiv_from
  r1 field r' r2
= has_struct_field_equiv_from' r1 field r' r2

let has_struct_field_equiv_to'
  (#opened: _)
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (r: ref (struct1 fields))
  (field: field_t)
  (r1': ref (fields.fd_typedef field))
  (r2': ref (fields.fd_typedef field))
: STGhostT unit opened
    (ref_equiv r1' r2' `star` has_struct_field1 r field r1')
    (fun _ -> ref_equiv r1' r2' `star` has_struct_field1 r field r2')
= rewrite (ref_equiv r1' r2') (ref_equiv0 r1' r2');
  let _ = gen_elim () in
  let w = vpattern_replace (fun w -> HR.pts_to r1' _ w `star` HR.pts_to r2' _ w) in
  rewrite (has_struct_field1 r field r1') (has_struct_field0 r field r1');
  let _ = gen_elim () in
  hr_gather w r1';
  hr_share r2';
  rewrite (has_struct_field0 r field r2') (has_struct_field1 r field r2');
  rewrite (ref_equiv0 r1' r2') (ref_equiv r1' r2')

let has_struct_field_equiv_to
  r field r1 r2
= has_struct_field_equiv_to' r field r1 r2

let ghost_struct_field_focus'
  (#opened: _)
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (#v: Ghost.erased (struct_t1 fields))
  (r: ref (struct1 fields))
  (field: field_t)
  (r': ref (fields.fd_typedef field))
: STGhostT unit opened
    (has_struct_field1 r field r' `star` pts_to r v)
    (fun _ -> has_struct_field1 r field r' `star` pts_to r (t_struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (t_struct_get_field v field))
= rewrite (has_struct_field1 r field r') (has_struct_field0 r field r');
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let w' = vpattern_replace (HR.pts_to r' _) in
  rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  hr_gather w r;
  rewrite (r_pts_to _ _) (R.pts_to w.ref (Ghost.reveal v));
  let prf
    (f': field_t)
    (x: (fields.fd_type f'))
  : Lemma
    (let p = (fields.fd_typedef f').pcm in
      composable p x (one p) /\
      op p x (one p) == x
    )
  = is_unit (fields.fd_typedef f').pcm x
  in
  Classical.forall_intro_2 prf;
  let v' = t_struct_set_field field (unknown (fields.fd_typedef field)) v in
  let vf = S.field_to_struct_f (struct_field_pcm _) field (t_struct_get_field v field) in
  assert (composable (struct_pcm _) v' vf);
  assert (op (struct_pcm _) v' vf `FX.feq` v);
  R.split w.ref _ v' vf;
  R.gfocus w.ref (S.struct_field (struct_field_pcm _) field) vf (t_struct_get_field v field);
  hr_share r;
  hr_share r';
  rewrite (has_struct_field0 r field r') (has_struct_field1 r field r');
  rewrite (pts_to0 r v') (pts_to r (t_struct_set_field field (unknown (fields.fd_typedef field)) v));
  rewrite (R.pts_to _ _) (r_pts_to w'.ref (t_struct_get_field v field));
  rewrite (pts_to0 r' (t_struct_get_field v field)) (pts_to r' (t_struct_get_field v field))
  
let ghost_struct_field_focus
  r field r'
= noop (); // FIXME: WHY WHY WHY? without this noop, z3 fails to prove precondition of field_description_t.fd_typedef . But also works if I put noop () after the function call
  ghost_struct_field_focus' r field r'

module GHR = Steel.ST.GhostHigherReference

let ghost_struct_field'
  (#opened: _)
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (#v: Ghost.erased (struct_t1 fields))
  (r: ref (struct1 fields))
  (field: field_t)
: STGhostT (Ghost.erased (ref (fields.fd_typedef field))) opened
    (pts_to r v)
    (fun r' -> pts_to r (t_struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (t_struct_get_field v field) `star` has_struct_field1 r field r')
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  rewrite (r_pts_to _ _) (r_pts_to w.ref (Ghost.reveal v));
  let w' = {
    base = w.base;
    ref = R.ref_focus w.ref (S.struct_field (struct_field_pcm (fields)) field);
  }
  in
  let gr' = GHR.alloc w' in
  let r1' = GHR.reveal_ref gr' in
  GHR.reveal_pts_to gr' P.full_perm w';
  rewrite_equiv (GHR.pts_to _ _ _) (HR.pts_to r1' P.full_perm w');
  HR.pts_to_not_null r1';
  let r' = Ghost.hide r1' in
  rewrite (HR.pts_to r1' P.full_perm w') (HR.pts_to r' P.full_perm w');
  hr_share r;
  rewrite (has_struct_field0 r field r') (has_struct_field1 r field r');
  rewrite (pts_to0 r (Ghost.reveal v)) (pts_to r v);
  ghost_struct_field_focus' r field r';
  r'

let ghost_struct_field
  r field
= noop (); // FIXME: WHY WHY WHY? (same as ghost_struct_field_focus above)
  ghost_struct_field' r field

let struct_field'
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (#v: Ghost.erased (struct_t1 fields))
  (r: ref (struct1 fields))
  (field: field_t)
: STT (ref (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> pts_to r (t_struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (t_struct_get_field v field) `star` has_struct_field1 r field r')
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = HR.read r in
  vpattern_rewrite (HR.pts_to r _) w;
  rewrite (r_pts_to _ _) (r_pts_to w.ref (Ghost.reveal v));
  let w' = {
    base = w.base;
    ref = R.ref_focus w.ref (S.struct_field (struct_field_pcm (fields)) field);
  }
  in
  let r' = HR.alloc w' in
  hr_share r;
  rewrite (has_struct_field0 r field r') (has_struct_field1 r field r');
  rewrite (pts_to0 r (Ghost.reveal v)) (pts_to r v);
  ghost_struct_field_focus' r field r';
  return r'

let struct_field0
  t' #_ #_ #v r field td'
= let r1' = struct_field' r field in
  let r' : ref td' = r1' in
  rewrite (pts_to r1' _) (pts_to r' (struct_get_field v field));
  rewrite (has_struct_field1 _ _ _) (has_struct_field r field r');
  return r'

let r_unfocus (#opened:_)
  (#ta #ta' #tb #tc: Type)
  (#p: pcm tb)
  (#q: pcm tc)
  (r: R.ref ta q) (r': R.ref ta' p)
  (l: Steel.C.Model.Connection.connection p q) (x: tc)
: STGhost (Ghost.erased tb) opened
    (r `R.pts_to` x)
    (fun x' -> r' `R.pts_to` x')
    (requires
      ta == ta' /\
      r == R.ref_focus r' l)
    (ensures fun x' -> Ghost.reveal x' == l.conn_small_to_large.morph x)
= let r1 : R.ref ta' q = r in
  rewrite (r `R.pts_to` x) (r1 `R.pts_to` x);
  R.unfocus r1 r' l x;
  let x' = vpattern_replace_erased (R.pts_to r') in
  x'

let unstruct_field'
  (#opened: _)
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (#v: Ghost.erased (struct_t1 fields))
  (r: ref (struct1 fields))
  (field: field_t)
  (#v': Ghost.erased (fields.fd_type field))
  (r': ref (fields.fd_typedef field))
: STGhost unit opened
    (has_struct_field1 r field r' `star` pts_to r v `star` pts_to r' v')
    (fun _ -> has_struct_field1 r field r' `star` pts_to r (t_struct_set_field field v' v))
    (
      t_struct_get_field v field == unknown (fields.fd_typedef field)
    )
    (fun _ -> True)
= rewrite (has_struct_field1 r field r') (has_struct_field0 r field r');
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let w' = vpattern_replace (HR.pts_to r' _) in
  rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  hr_gather w r;
  rewrite (r_pts_to _ (Ghost.reveal v)) (R.pts_to w.ref (Ghost.reveal v));
  rewrite (pts_to r' v') (pts_to0 r' v');
  let _ = gen_elim () in
  hr_gather w' r';
  rewrite (r_pts_to _ (Ghost.reveal v')) (R.pts_to w'.ref (Ghost.reveal v'));
  let prf
    (f': field_t)
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
  assert (op (struct_pcm _) v vf `FX.feq` t_struct_set_field field v' v);
  let _ = r_unfocus w'.ref w.ref (coerce_eq () (S.struct_field (struct_field_pcm fields) field)) _ in
  let _ = R.gather w.ref (Ghost.reveal v) _ in
  hr_share r;
  rewrite (has_struct_field0 r field r') (has_struct_field1 r field r');
  rewrite (pts_to0 r _) (pts_to r _)

let unstruct_field
  r field r'
= unstruct_field' r field r'

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

module U = Steel.ST.C.Model.Union

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

let has_union_field_gen
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref0_v (union0 tn n fields))
  (field: field_t fields)
  (r': ref0_v (fields.fd_typedef field))
: GTot prop
= r'.base == r.base /\
  r'.ref == R.ref_focus r.ref (U.union_field (union_field_pcm fields) (Some field))

[@@__reduce__]
let has_union_field0
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (r': ref (fields.fd_typedef field))
: Tot vprop
= exists_ (fun p -> exists_ (fun w -> exists_ (fun p' -> exists_ (fun w' ->
    HR.pts_to r p w `star`
    HR.pts_to r' p' w' `star`
    pure (has_union_field_gen w field w')
  ))))

let has_union_field
  r field r'
= has_union_field0 r field r'

#push-options "--split_queries"

let has_union_field_dup
  r field r'
= rewrite (has_union_field r field r') (has_union_field0 r field r');
  let _ = gen_elim () in
  hr_share r;
  hr_share r';
  noop ();
  rewrite (has_union_field0 r field r') (has_union_field r field r');
  noop ();
  rewrite (has_union_field0 r field r') (has_union_field r field r')

#push-options "--z3rlimit 16"

let has_union_field_inj
  r field r1 r2
= rewrite (has_union_field r field r1) (has_union_field0 r field r1);
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  rewrite (has_union_field r field r2) (has_union_field0 r field r2);
  let _ = gen_elim () in
  hr_gather w r;
  hr_share r;
  hr_share r1;
  rewrite (has_union_field0 r field r1) (has_union_field r field r1);
  hr_share r2;
  rewrite (has_union_field0 r field r2) (has_union_field r field r2);
  let w' = vpattern_replace (HR.pts_to r1 _) in
  vpattern_rewrite (HR.pts_to r2 _) w';
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

#pop-options

let has_union_field_equiv_from
  r1 r2 field r'
= rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = gen_elim () in
  let w = vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  rewrite (has_union_field r1 field r') (has_union_field0 r1 field r');
  let _ = gen_elim () in
  hr_gather w r1;
  hr_share r2;
  rewrite (has_union_field0 r2 field r') (has_union_field r2 field r');
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let has_union_field_equiv_to
  r field r1' r2'
= rewrite (ref_equiv r1' r2') (ref_equiv0 r1' r2');
  let _ = gen_elim () in
  let w = vpattern_replace (fun w -> HR.pts_to r1' _ w `star` HR.pts_to r2' _ w) in
  rewrite (has_union_field r field r1') (has_union_field0 r field r1');
  let _ = gen_elim () in
  hr_gather w r1';
  hr_share r2';
  rewrite (has_union_field0 r field r2') (has_union_field r field r2');
  rewrite (ref_equiv0 r1' r2') (ref_equiv r1' r2')

#push-options "--z3rlimit 16"

#restart-solver

let ghost_union_field_focus
  #_ #tn #_ #n #fields #v r field r'
= rewrite (has_union_field r field r') (has_union_field0 r field r');
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let w' = vpattern_replace (HR.pts_to r' _) in
  rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  hr_gather w r;
  rewrite (r_pts_to _ _) (R.pts_to w.ref (Ghost.reveal v));
  let v' = U.field_to_union_f (union_field_pcm fields) (Some field) (union_get_field v field) in
  assert (v' `FX.feq` v);
  R.gfocus w.ref (U.union_field (union_field_pcm fields) (Some field)) v (union_get_field v field);
  rewrite (R.pts_to _ _) (R.pts_to w'.ref (union_get_field v field));
  hr_share r';
  rewrite (pts_to0 r' _) (pts_to r' _);
  rewrite (has_union_field0 r field r') (has_union_field r field r')

let ghost_union_field
  #_ #tn #_ #n #fields #v r field
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  rewrite (r_pts_to _ _) (r_pts_to w.ref (Ghost.reveal v));
  let w' = {
    base = w.base;
    ref = R.ref_focus w.ref (U.union_field (union_field_pcm (fields)) (Some field));
  }
  in
  let gr' = GHR.alloc w' in
  let r1' = GHR.reveal_ref gr' in
  GHR.reveal_pts_to gr' P.full_perm w';
  rewrite_equiv (GHR.pts_to _ _ _) (HR.pts_to r1' P.full_perm w');
  HR.pts_to_not_null r1';
  let r' = Ghost.hide r1' in
  rewrite (HR.pts_to r1' P.full_perm w') (HR.pts_to r' P.full_perm w');
  hr_share r;
  rewrite (has_union_field0 r field r') (has_union_field r field r');
  rewrite (pts_to0 r (Ghost.reveal v)) (pts_to r v);
  ghost_union_field_focus r field r';
  r'

[@@noextract_to "krml"] // primitive
let union_field'
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
: STT (ref (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (union_get_field v field))
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = HR.read r in
  vpattern_rewrite (HR.pts_to r _) w;
  rewrite (r_pts_to _ _) (r_pts_to w.ref (Ghost.reveal v));
  let w' = {
    base = w.base;
    ref = R.ref_focus w.ref (U.union_field (union_field_pcm (fields)) (Some field));
  }
  in
  let r' = HR.alloc w' in
  hr_share r;
  rewrite (has_union_field0 r field r') (has_union_field r field r');
  rewrite (pts_to0 r (Ghost.reveal v)) (pts_to r v);
  ghost_union_field_focus r field r';
  return r'

let union_field0
  t' r field td'
=
  let r' = union_field' r field in
  let res : ref td' = r' in
  rewrite (pts_to r' _) (pts_to res _);
  rewrite (has_union_field r field _) (has_union_field r field res);
  return res

#pop-options


#push-options "--z3rlimit 32"

#restart-solver

let ununion_field
  #_ #tn #_ #n #fields r field #v' r'
= rewrite (has_union_field r field r') (has_union_field0 r field r');
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let w' = vpattern_replace (HR.pts_to r' _) in
  rewrite (pts_to r' v') (pts_to0 r' v');
  let _= gen_elim () in
  hr_gather w' r';
  rewrite (r_pts_to _ _) (R.pts_to w'.ref (Ghost.reveal v'));
  let _ = r_unfocus w'.ref w.ref (coerce_eq () (U.union_field (union_field_pcm fields) (Some field))) _ in
  hr_share r;
  rewrite (has_union_field0 r field r') (has_union_field r field r');
  rewrite (R.pts_to _ _) (R.pts_to w.ref (union_set_field tn n fields field (Ghost.reveal v')));
  rewrite (pts_to0 r (union_set_field tn n fields field (Ghost.reveal v'))) (pts_to r (union_set_field tn n fields field (Ghost.reveal v')))

[@@noextract_to "krml"] // primitive
let union_switch_field'
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields)
: ST (ref (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (uninitialized (fields.fd_typedef field)))
    (full (union0 tn n fields) v)
    (fun _ -> True)
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = HR.read r in
  vpattern_rewrite (HR.pts_to r _) w;
  rewrite (r_pts_to _ _) (R.pts_to w.ref (Ghost.reveal v));
  let v' : union_t0 tn n fields = U.field_to_union_f (union_field_pcm fields) (Some field) (fields.fd_typedef field).uninitialized in
  R.ref_upd w.ref _ _ (R.base_fpu (union_pcm tn n fields) _ v');
  rewrite (pts_to0 r v') (pts_to r v');
  let r' = union_field' r field in
  rewrite (pts_to r' _) (pts_to r' (uninitialized (fields.fd_typedef field)));
  return r'

#pop-options

[@@noextract_to "krml"] // primitive
let union_switch_field0'
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (td': typedef t')
  (sq: squash (
    t' ==  fields.fd_type field /\
    td' == fields.fd_typedef field
  ))
: ST (ref td') // need to write the pcm carrier value, so this cannot be Ghost or Atomic
    (pts_to r v)
    (fun r' -> has_union_field r field (coerce_eq () r') `star` pts_to r' (Ghost.hide (coerce_eq () (uninitialized (fields.fd_typedef field)))))
    (full (union0 tn n fields) v)
    (fun _ -> True)
= let r' = union_switch_field' #tn #tf #n #fields #v r field in
  let res : ref td' = r' in
  rewrite (pts_to r' _) (pts_to res (Ghost.hide (coerce_eq () (uninitialized (fields.fd_typedef field)))));
  rewrite (has_union_field r field _) (has_union_field r field (coerce_eq () res));
  return res

let union_switch_field0
  t' r field td'
= union_switch_field0' t' r field td' ()

#pop-options


/// Base arrays (without decay: explicit array types as top-level arrays or struct/union fields of array type)

module A = Steel.ST.C.Model.Array

let base_array_t'
  (t: Type0)
  (n: Ghost.erased array_size_t)
: Tot Type0
= A.array_pcm_carrier t (Ghost.hide (Ghost.reveal n))

let base_array_t t _ n = base_array_t' t n

[@@noextract_to "krml"] // proof-only
let base_array_fd
  (#t: Type)
  (td: typedef t)
  (n: Ghost.erased array_size_t)
: Tot (field_description_gen_t (base_array_index_t n))
= {
    fd_nonempty = (let _ : base_array_index_t n = 0sz in ());
    fd_type = A.array_range t (Ghost.hide (Ghost.reveal n));
    fd_typedef = (fun _ -> td);
  }

[@@noextract_to "krml"]
let base_array1 (#t: Type0) (td: typedef t) (n: Ghost.erased array_size_t) : Tot (typedef (base_array_t' t n)) = struct1 (base_array_fd td n)

let base_array0 tn td n = base_array1 td n

let base_array_index a i = a i

let base_array_eq #_ #_ #n a1 a2 =
  assert (a1 `FX.feq` a2 <==> (forall (i: base_array_index_t n) . a1 i == a2 i));
  a1 `FX.feq` a2

let mk_base_array _ n v = A.array_pcm_carrier_of_seq n v

let mk_base_array_index _ _ _ _ = ()

let base_array_fractionable a td = ()

let base_array_mk_fraction a td p i = ()

let base_array_index_unknown tn n td i = ()

let base_array_index_uninitialized tn n td i = ()

let base_array_index_full td x = ()

let base_array_index_t' (n: Ghost.erased array_size_t) : Tot eqtype =
  A.array_domain (Ghost.hide (Ghost.reveal n))

let base_array_index_t'_eq
  (n: array_size_t)
: Lemma
  (base_array_index_t n == base_array_index_t' n)
  [SMTPat (base_array_index_t n)]
= // syntactic equality of refinement types
  assert (base_array_index_t n == base_array_index_t' n) by (FStar.Tactics.trefl ())

let array_index_as_field_marker
  (n: Ghost.erased array_size_t)
  (i: SZ.t)
  (j: base_array_index_t' n)
: Tot (base_array_index_t' n)
= j

#set-options "--print_implicits"

let base_array1_eq
  (#t: Type)
  (n: Ghost.erased array_size_t)
  (td: typedef t)
: Lemma
  (ref (base_array1 td n) == ref (struct1 #(base_array_index_t' n) (base_array_fd td n)))
//  [SMTPat (ref (base_array1 td n))]
= () // assert (ref (base_array1 td n) == ref (struct1 #(base_array_index_t' n) (base_array_fd td n))) by (FStar.Tactics.trefl ())

[@@__reduce__]
let has_base_array_cell_as_struct_field0
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (j: base_array_index_t' n)
  (r': ref td)
: Tot vprop
= has_struct_field1 #(base_array_index_t' n) #(base_array_fd td n) r (array_index_as_field_marker n i j) r'

let has_base_array_cell_as_struct_field
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (j: base_array_index_t' n)
  (r': ref td)
: Tot vprop
= has_base_array_cell_as_struct_field0 r i j r'

[@@__reduce__]
let has_base_array_cell0
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (r': ref td)
: Tot vprop
= exists_ (fun j ->
    has_base_array_cell_as_struct_field r i j r' `star`
    pure (i == j)
  )

let has_base_array_cell1
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (r': ref td)
: Tot vprop
= has_base_array_cell0 r i r'

let has_base_array_cell
  r i r'
= has_base_array_cell0 r i r'

let has_base_array_cell_post
  r i r'
= rewrite (has_base_array_cell r i r') (has_base_array_cell0 r i r');
  let _ = gen_elim () in
  rewrite (has_base_array_cell0 r i r') (has_base_array_cell r i r')

let has_base_array_cell_dup'
  (#opened: _)
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (r': ref td)
: STGhostT unit opened
    (has_base_array_cell1 r i r')
    (fun _ -> has_base_array_cell1 r i r' `star` has_base_array_cell1 r i r')
= rewrite (has_base_array_cell1 r i r') (has_base_array_cell0 r i r');
  let _ = gen_elim () in
  has_struct_field_dup'  #_ #(base_array_index_t' n) #(base_array_fd td n) (r) _ _;
  rewrite (has_base_array_cell0 r i r') (has_base_array_cell1 r i r');
  noop ();
  rewrite (has_base_array_cell0 r i r') (has_base_array_cell1 r i r')

let has_base_array_cell_dup
  r i r'
= has_base_array_cell_dup' r i r'

let has_base_array_cell_inj'
  (#opened: _)
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (r1 r2: ref td)
: STGhostT unit opened
    (has_base_array_cell1 r i r1 `star` has_base_array_cell1 r i r2)
    (fun _ -> has_base_array_cell1 r i r1 `star` has_base_array_cell1 r i r2 `star` ref_equiv r1 r2)
= rewrite (has_base_array_cell1 r i r1) (has_base_array_cell0 r i r1);
  let _ = gen_elim () in
  let j = vpattern_replace (fun j -> has_base_array_cell_as_struct_field r i j _) in
  rewrite (has_base_array_cell1 r i r2) (has_base_array_cell0 r i r2);
  let _ = gen_elim () in
  vpattern_rewrite (fun j' -> has_base_array_cell_as_struct_field r i j _ `star` has_base_array_cell_as_struct_field r i j' _) j;
  has_struct_field_inj' #_ #(base_array_index_t' n) #(base_array_fd td n) (r) _ r1 r2;
  rewrite (has_base_array_cell0 r i r2) (has_base_array_cell1 r i r2);
  rewrite (has_base_array_cell0 r i r1) (has_base_array_cell1 r i r1)

let has_base_array_cell_inj
  r i r1 r2
= has_base_array_cell_inj' r i r1 r2

let has_base_array_cell_equiv_from'
  (#opened: _)
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r1 r2: ref (base_array1 td n))
  (i: SZ.t)
  (r': ref td)
: STGhostT unit opened
    (has_base_array_cell1 r1 i r' `star` ref_equiv r1 r2)
    (fun _ -> has_base_array_cell1 r2 i r' `star` ref_equiv r1 r2)
= rewrite (has_base_array_cell1 r1 i r') (has_base_array_cell0 r1 i r');
  let _ = gen_elim () in
  has_struct_field_equiv_from'  #_ #(base_array_index_t' n) #(base_array_fd td n) (r1) _ r' (r2);
  rewrite (has_base_array_cell0 r2 i r') (has_base_array_cell1 r2 i r')

let has_base_array_cell_equiv_from
  r1 r2 i r'
= has_base_array_cell_equiv_from' r1 r2 i r'

let has_base_array_cell_equiv_to'
  (#opened: _)
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (r1 r2: ref td)
: STGhostT unit opened
    (has_base_array_cell1 r i r1 `star` ref_equiv r1 r2)
    (fun _ -> has_base_array_cell1 r i r2 `star` ref_equiv r1 r2)
= rewrite (has_base_array_cell1 r i r1) (has_base_array_cell0 r i r1);
  let _ = gen_elim () in
  has_struct_field_equiv_to' r _ r1 r2;
  rewrite (has_base_array_cell0 r i r2) (has_base_array_cell1 r i r2)

let has_base_array_cell_equiv_to
  r i r1 r2
= has_base_array_cell_equiv_to' r i r1 r2

/// Array pointers (with decay)

noeq
type array_ref #t td = {
  ar_base_size: Ghost.erased array_size_t;
  ar_base: ref (base_array1 #t td ar_base_size);
  ar_offset: SZ.t;
  ar_prf: squash (SZ.v ar_offset <= SZ.v ar_base_size);
}
let array_ref_base_size ar = ar.ar_base_size
let has_array_ref_base ar r = ar.ar_base == r
let has_array_ref_base_inj ar r1 r2 = ()
let array_ref_offset ar = ar.ar_offset
let array_ref_base_offset_inj a1 r1 a2 r2 = ()

let base_array_pcm_eq
  (#t: Type)
  (td: typedef t)
  (n: Ghost.erased array_size_t)
: Lemma
  (A.array_pcm td.pcm (Ghost.hide (Ghost.reveal n)) == (base_array1 td n).pcm)
  [SMTPat (base_array1 td n).pcm]
= pcm0_ext (A.array_pcm td.pcm (Ghost.hide (Ghost.reveal n))) (base_array1 td n).pcm
    (fun _ _ -> ())
    (fun x1 x2 ->
      assert (op (A.array_pcm td.pcm (Ghost.hide (Ghost.reveal n))) x1 x2 `FX.feq` op (base_array1 td n).pcm x1 x2)
    )
    (fun _ -> ())
    ()

[@@noextract_to "krml"] // proof-only
let model_array_of_array
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (base: ref0_v (base_array1 td (dfst a).ar_base_size))
: Tot (A.array base.base td.pcm)
= let (| al, len |) = a in
  {
    base_len = Ghost.hide (Ghost.reveal al.ar_base_size);
    base = base.ref;
    offset = al.ar_offset;
    len = len;
    prf = ();
  }

[@@__reduce__]
let array_pts_to0
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
: Tot vprop
= exists_ (fun br -> exists_ (fun p ->
    HR.pts_to (dfst r).ar_base p br `star`
    A.pts_to (model_array_of_array r br) v
  ))

let array_pts_to r v =
  array_pts_to0 r v

let array_pts_to_length r v =
  rewrite (array_pts_to r v) (array_pts_to0 r v);
  let _ = gen_elim () in
  let _ = A.pts_to_length _ _ in
  rewrite (array_pts_to0 r v) (array_pts_to r v)

#push-options "--z3rlimit 16"
#restart-solver

let ghost_array_of_base_focus
  #_ #_ #_ #_ #td #v r a
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let w' : ref0_v (base_array1 td (dfst a).ar_base_size) = coerce_eq () w in
  assert ((model_array_of_array a w').base == w.ref);
  rewrite (r_pts_to _ _) (R.pts_to (model_array_of_array a w').base v);
  assert (seq_of_base_array v `Seq.equal` A.seq_of_array_pcm_carrier v);
  A.array_pcm_carrier_of_seq_of_array_pcm_carrier v;
  A.pts_to_intro_from_base (model_array_of_array a w')  v (seq_of_base_array v);
  let p = vpattern_replace (fun p -> HR.pts_to _ p _) in
  rewrite (HR.pts_to _ _ _) (HR.pts_to (dfst a).ar_base p w');
  rewrite (array_pts_to0 a (seq_of_base_array v)) (array_pts_to a (seq_of_base_array v))

#pop-options

let ghost_array_of_base
  #_ #tn #_ #n #td #v r
=
  let al : array_ref td = {
    ar_base_size = n;
    ar_base = r;
    ar_offset = 0sz;
    ar_prf = ();
  }
  in
  let a : (a: Ghost.erased (array td) { has_array_of_base r a }) = (| al, Ghost.hide (Ghost.reveal n) |) in
  ghost_array_of_base_focus r a;
  a

[@@noextract_to "krml"] // primitive
let array_of_base0
  (#t: Type)
  (#tn: Type0)
  (#opened: _)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
: STAtomicBase (a: array td { has_array_of_base r a }) false opened Unobservable
    (pts_to r v)
    (fun a -> array_pts_to a (seq_of_base_array v))
    (True)
    (fun _ -> True)
=
  let al : array_ref td = {
    ar_base_size = n;
    ar_base = r;
    ar_offset = 0sz;
    ar_prf = ();
  }
  in
  let a : (a: array td { has_array_of_base r a }) = (| al, Ghost.hide (Ghost.reveal n) |) in
  ghost_array_of_base_focus r a;
  return a

let array_ref_of_base
  #_ #tn #_ #n #td #v r
=
  let ar = array_of_base0 r in
  let a : array_ref td = dfst ar in
  return a

#push-options "--z3rlimit 16 --split_queries"

#restart-solver

let base_array_index' (#t: Type0) (#n: array_size_t) (a: base_array_t' t n)
(i: base_array_index_t n) : GTot t
= a i

let seq_of_base_array0
  (#t: Type)
  (#n: array_size_t)
  (v: base_array_t' t n)
: GTot (Seq.lseq t (SZ.v n))
= Seq.init_ghost (SZ.v n) (fun i -> base_array_index' v (SZ.uint_to_t i))

let has_array_of_base'
  (#t: Type)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (a: array td)
: GTot prop
=   let (| al, len |) = a in
    array_ref_base_size al == n /\
    al.ar_base == r /\
    array_ref_offset al == 0sz /\
    Ghost.reveal len == n

#pop-options

#push-options "--z3rlimit 64"
#restart-solver

let unarray_of_base0
  (#t: Type)
  (#opened: _)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: ref (base_array1 td n))
  (a: array td)
: STGhost (Ghost.erased (base_array_t' t n)) opened
    (array_pts_to a v)
    (fun v' -> pts_to r v')
    (
      has_array_of_base' r a
    )
    (fun v' -> Ghost.reveal v `Seq.equal` seq_of_base_array0 v')
= rewrite (array_pts_to a v) (array_pts_to0 a v);
  let _ = gen_elim () in
  let p = vpattern_replace (fun p -> HR.pts_to _ p _) in
  let ba = vpattern_replace (HR.pts_to _ _) in
  let ba' : ref0_v (base_array1 td n) = coerce_eq () ba in
  rewrite (HR.pts_to _ _ _) (HR.pts_to r p ba');
  let m = model_array_of_array a ba in
  rewrite (A.pts_to _ _) (A.pts_to m v);
  let y : Ghost.erased (A.array_pcm_carrier t m.base_len) = A.pts_to_elim_to_base m v in
  let y' : Ghost.erased (base_array_t' t n) = Ghost.hide (Ghost.reveal y) in
  rewrite (r_pts_to _ _) (r_pts_to ba'.ref (Ghost.reveal y'));
  rewrite (pts_to0 r y') (pts_to r y');
  y'

#pop-options

let unarray_of_base
  #t #tn #_ #n #td #v r a
= unarray_of_base0 r a

(*
let has_array_of_ref
  r a
= TD.type_of_token (dfst a).ar_base_size_token == unit /\
  model_array_of_array a == A.g_array_of_ref (coerce _ (Some?.v r).ref)

let has_array_of_ref_inj
  r a1 a2
= TD.type_of_token_inj (dfst a1).ar_base_size_token (dfst a2).ar_base_size_token;
  TD.type_of_token_inj (Some?.v (dfst a1).ar_base).dest (Some?.v (dfst a2).ar_base).dest

let ghost_array_of_ref_focus
  #t #_ #td #v r a
= let mr : R.ref td.pcm = (Some?.v r).ref in
  rewrite_slprop (pts_to _ _) (R.pts_to mr v) (fun _ -> ());
  let ma = A.ghost_array_of_ref mr in
  rewrite_slprop (A.pts_to _ _) (array_pts_to _ _) (fun _ -> ())

let ghost_array_of_ref
  #t #_ #td #v r
= let mr : R.ref td.pcm = (Some?.v r).ref in
  let ma = A.g_array_of_ref mr in
  let tok_unit = TD.get_token unit in
  let tok_array = TD.get_token (A.array_pcm_carrier t 1sz) in
  let ar = {
    ar_base_size_token = tok_unit;
    ar_base_size = 1sz;
    ar_base = Some ({
      dest = tok_array;
      typedef = base_array0 unit td 1sz;
      ref = coerce _ ma.base;
    });
    ar_offset = 0sz;
  }
  in
  let res: (a: Ghost.erased (array td) { has_array_of_ref r a }) = Ghost.hide (| ar, Ghost.hide 1sz |) in
  ghost_array_of_ref_focus r res;
  res

let array_ref_of_ref
  #t #_ #td #v r
= let mr : R.ref td.pcm = (Some?.v r).ref in
  rewrite_slprop (pts_to _ _) (R.pts_to mr v) (fun _ -> ());
  let ma = A.array_of_ref mr in
  let tok_unit = TD.get_token unit in
  let tok_array = TD.get_token (A.array_pcm_carrier t 1sz) in
  let res = {
    ar_base_size_token = tok_unit;
    ar_base_size = 1sz;
    ar_base = Some ({
      dest = tok_array;
      typedef = base_array0 unit td 1sz;
      ref = coerce _ ma.base;
    });
    ar_offset = 0sz;
  }
  in
  rewrite_slprop (A.pts_to _ _) (array_pts_to _ _) (fun _ -> ());
  return res

let unarray_of_ref = magic ()
*)

[@@noextract_to "krml"]
let array_index_as_base_array_index_marker
  (index: SZ.t)
  (base_index: SZ.t)
: Tot SZ.t
= base_index

[@@__reduce__]
let has_array_cell0
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: Tot vprop
= exists_ (fun (j: SZ.t) ->
    has_base_array_cell1 (dfst a).ar_base (array_index_as_base_array_index_marker i j) r `star`
    pure (
      SZ.v j == SZ.v ((dfst a).ar_offset) + SZ.v i /\
      SZ.v i < SZ.v (dsnd a)
    )
  )

let has_array_cell1
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: Tot vprop
= has_array_cell0 a i r

let has_array_cell
  a i r
= has_array_cell0 a i r

let has_array_cell_post
  a i r
= rewrite (has_array_cell a i r) (has_array_cell0 a i r);
  let _ = gen_elim () in
  rewrite (has_array_cell0 a i r) (has_array_cell a i r)

let has_array_cell_has_base_array_cell
  a i r br
= rewrite (has_array_cell a i r) (has_array_cell0 a i r);
  let _ = gen_elim () in
  let j = vpattern_replace_erased (fun j -> has_base_array_cell1 _ j r) in
  rewrite (has_base_array_cell1 _ _ _) (has_base_array_cell br j r);
  j

let has_base_array_cell_has_array_cell
  a i r br
= let j : Ghost.erased SZ.t = Ghost.hide (i `SZ.sub` (dfst a).ar_offset) in
  rewrite (has_base_array_cell br i r) (has_base_array_cell1 (dfst a).ar_base (array_index_as_base_array_index_marker j i) r);
  rewrite (has_array_cell0 a j r) (has_array_cell a j r);
  j

let has_array_cell_inj
  #_ #_ #td a i r1 r2
= has_array_cell_post a i r1;
  let br : ref (base_array0 unit (* dummy *) td (array_ref_base_size (dfst a))) = (dfst a).ar_base in
  let j1 = has_array_cell_has_base_array_cell a i r1 br in
  let j2 = has_array_cell_has_base_array_cell a i r2 br in
  vpattern_rewrite (fun j2 -> has_base_array_cell _ j2 r2) j1;
  has_base_array_cell_inj br j1 r1 r2;
  let _ = has_base_array_cell_has_array_cell a j1 r1 br in
  vpattern_rewrite (fun i -> has_array_cell _ i r1) i;
  let _ = has_base_array_cell_has_array_cell a j1 r2 br in
  vpattern_rewrite (fun i -> has_array_cell _ i r2) i
  

#restart-solver
let struct_field_eq_cell
  (#t: Type)
  (td: typedef t)
  (n: array_size_t)
  (k: base_array_index_t n)
: Lemma
  (Steel.ST.C.Model.Struct.struct_field (struct_field_pcm (base_array_fd td n)) k == A.cell td.pcm n k)
= // assert_norm (A.array_domain n == base_array_index_t n);
  Steel.ST.C.Model.Struct.struct_field_ext #(A.array_domain n) #(A.array_range t n) (struct_field_pcm (base_array_fd td n)) (A.array_elements_pcm td.pcm n) (fun _ -> ()) k

(*
#push-options "--split_queries --z3rlimit 16"

#restart-solver
let has_array_cell_array_of_ref
  #_ #td r a
= assert_norm (SZ.v 0sz == 0);
  assert_norm (SZ.v 1sz == 1);
  A.ref_of_array_of_ref (Some?.v r).ref;
  A.ref_of_array_of_ref_base (Some?.v r).ref;
  assert (Ghost.reveal (dsnd a) == 1sz);
  assert ((dfst a).ar_offset == 0sz);
  struct_field_eq_cell td 1sz 0sz;
  assert (has_base_array_cell0 (array_ref_base (dfst a)) (array_ref_offset (dfst a) `SZ.add` 0sz) r)

#pop-options
*)

let has_struct_field1_intro
  (#opened: _)
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (r: ref (struct1 fields))
  (field: field_t)
  (r': ref (fields.fd_typedef field))
  (p: P.perm)
  (w: ref0_v (struct1 fields))
  (p': P.perm)
  (w': ref0_v (fields.fd_typedef field))
  ()
: STGhost unit opened
    (HR.pts_to r p w `star` HR.pts_to r' p' w')
    (fun _ ->
      has_struct_field1 r field r'
    )
    (
      has_struct_field_gen fields w field w'
    )
    (fun _ -> True)
= noop ();
  rewrite
    (has_struct_field0 r field r')
    (has_struct_field1 r field r')

let has_array_cell_drop
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (#p': P.perm)
  (#b': ref0_v td)
  (i: SZ.t)
  (r: ref td)
: STGhostT unit opened
    (has_array_cell1 a i r `star`
      HR.pts_to r p' b'
    )
    (fun _ -> has_array_cell1 a i r)
= rewrite (has_array_cell1 a i r) (has_array_cell0 a i r);
  let _ = gen_elim () in
  let j = vpattern_replace (fun j -> has_base_array_cell1 _ j _) in
  rewrite (has_base_array_cell1 (dfst a).ar_base j r) (has_base_array_cell0 (dfst a).ar_base j r);
  let _ = gen_elim () in
  let j' : base_array_index_t' (dfst a).ar_base_size = vpattern_replace (fun j' -> has_base_array_cell_as_struct_field _ _ j' _) in
  rewrite (has_base_array_cell_as_struct_field (dfst a).ar_base j j' r) (has_struct_field0 #(base_array_index_t' (dfst a).ar_base_size) #(base_array_fd td (dfst a).ar_base_size) (dfst a).ar_base j' r);
  let _ = gen_elim () in
  HR.gather p' r;
  has_struct_field1_intro
    #_ #(base_array_index_t' (dfst a).ar_base_size) #(base_array_fd td (dfst a).ar_base_size) (dfst a).ar_base j' r _ _ _ _ ();
  rewrite
    (has_struct_field1 #(base_array_index_t' (dfst a).ar_base_size) #(base_array_fd td (dfst a).ar_base_size) (dfst a).ar_base j' r)
    (has_base_array_cell_as_struct_field (dfst a).ar_base j j' r);
  rewrite
    (has_base_array_cell0 (dfst a).ar_base j r)
    (has_base_array_cell1 (dfst a).ar_base (array_index_as_base_array_index_marker i j) r);
  rewrite
    (has_array_cell0 a i r)
    (has_array_cell a i r)

let has_array_cell_elim
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#p: P.perm)
  (a: array td)
  (#b: ref0_v (base_array1 td (dfst a).ar_base_size))
  (i: SZ.t)
  (r: ref td)
: STGhost (Ghost.erased (ref0_v td)) opened
    (has_array_cell1 a i r `star`
      HR.pts_to (dfst a).ar_base p b
    )
    (fun b' -> has_array_cell1 a i r `star`
      exists_ (fun p -> exists_ (fun p' ->
        HR.pts_to (dfst a).ar_base p b `star`
        HR.pts_to r p' b'
    )))
    True
    (fun b' ->
      let ar = model_array_of_array a b in
      SZ.v i < SZ.v ar.len /\
      b'.base == b.base /\
      b'.ref == R.ref_focus (A.ref_of_array ar) (A.cell td.pcm ar.len i)
    )
= 
  rewrite (has_array_cell1 a i r) (has_array_cell0 a i r);
  let _ = gen_elim () in
  let j = vpattern_replace (fun j -> has_base_array_cell1 _ j _) in
  rewrite (has_base_array_cell1 (dfst a).ar_base j r) (has_base_array_cell0 (dfst a).ar_base j r);
  let _ = gen_elim () in
  let j' : base_array_index_t' (dfst a).ar_base_size = vpattern_replace (fun j' -> has_base_array_cell_as_struct_field _ _ j' _) in
  rewrite (has_base_array_cell_as_struct_field (dfst a).ar_base j j' r) (has_struct_field0 #(base_array_index_t' (dfst a).ar_base_size) #(base_array_fd td (dfst a).ar_base_size) (dfst a).ar_base j' r);
  let _ = gen_elim () in
  hr_gather b (dfst a).ar_base;
  HR.share r;
  HR.share (dfst a).ar_base;
  has_struct_field1_intro #_ #(base_array_index_t' (dfst a).ar_base_size) #(base_array_fd td (dfst a).ar_base_size) (dfst a).ar_base j' r _ _ _ _ ();
  rewrite (has_struct_field1 #(base_array_index_t' (dfst a).ar_base_size) #(base_array_fd td (dfst a).ar_base_size) (dfst a).ar_base j' r) (has_base_array_cell_as_struct_field (dfst a).ar_base j j' r);
  rewrite
    (has_base_array_cell0 (dfst a).ar_base j r)
    (has_base_array_cell1 (dfst a).ar_base (array_index_as_base_array_index_marker i j) r);
  rewrite
    (has_array_cell0 a i r)
    (has_array_cell a i r);
  A.ref_of_array_eq (model_array_of_array a b) i;
  struct_field_eq_cell td (dfst a).ar_base_size j';
  let b' = vpattern_replace_erased (HR.pts_to r _) in
  noop ();
  b'

let ghost_array_cell_focus
  #_ #_ #td #s a i r
= rewrite (array_pts_to a s) (array_pts_to0 a s);
  let _ = gen_elim () in
  let b = vpattern_replace (HR.pts_to (dfst a).ar_base _) in
  let r' = has_array_cell_elim a i r in
  let _ = gen_elim () in
  let _ = A.g_focus_cell _ _ i () in
  rewrite (R.pts_to _ _) (R.pts_to r'.ref (Seq.index s (SZ.v i)));
  rewrite (pts_to0 r (Seq.index s (SZ.v i))) (pts_to r (Seq.index s (SZ.v i)));
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array a b) (Seq.upd s (SZ.v i) (unknown td)));
  rewrite (array_pts_to0 a (Seq.upd s (SZ.v i) (unknown td))) (array_pts_to a (Seq.upd s (SZ.v i) (unknown td)))

let has_array_cell_intro
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#p: P.perm)
  (a: array td)
  (#b: ref0_v (base_array1 td (dfst a).ar_base_size))
  (#p': P.perm)
  (#b': ref0_v td)
  (i: SZ.t)
  (r: ref td)
: STGhost unit opened
    (HR.pts_to (dfst a).ar_base p b `star`
      HR.pts_to r p' b'
    )
    (fun _ -> has_array_cell1 a i r)
    (
      let ar = model_array_of_array a b in
      SZ.v i < SZ.v ar.len /\
      b'.base == b.base /\
      b'.ref == R.ref_focus (A.ref_of_array ar) (A.cell td.pcm ar.len i)
    )
    (fun _ -> True)
= 
  A.ref_of_array_eq (model_array_of_array a b) i;
  let j : base_array_index_t' (dfst a).ar_base_size = (dfst a).ar_offset `SZ.add` i in
  struct_field_eq_cell td (dfst a).ar_base_size j;
  has_struct_field1_intro #_ #(base_array_index_t' (dfst a).ar_base_size) #(base_array_fd td (dfst a).ar_base_size) (dfst a).ar_base j r _ _ _ _ ();
  rewrite (has_struct_field1 #(base_array_index_t' (dfst a).ar_base_size) #(base_array_fd td (dfst a).ar_base_size) (dfst a).ar_base j r) (has_base_array_cell_as_struct_field (dfst a).ar_base j j r);
  rewrite
    (has_base_array_cell0 (dfst a).ar_base j r)
    (has_base_array_cell1 (dfst a).ar_base (array_index_as_base_array_index_marker i j) r);
  rewrite
    (has_array_cell0 a i r)
    (has_array_cell a i r)

let ghost_array_cell
  #_ #_ #td #s a i
= array_pts_to_length _ _;
  rewrite (array_pts_to a s) (array_pts_to0 a s);
  let _ = gen_elim () in
  HR.share _;
  rewrite (array_pts_to0 a s) (array_pts_to a s);
  let b = vpattern_replace (HR.pts_to (dfst a).ar_base _) in
  let ar = model_array_of_array a b in
  let b' = {
    base = b.base;
    ref = R.ref_focus (A.ref_of_array ar) (A.cell td.pcm ar.len i);
  }
  in
  let ghr = GHR.alloc b' in
  GHR.reveal_pts_to ghr P.full_perm b';
  let hr = GHR.reveal_ref ghr in
  rewrite_equiv (GHR.pts_to _ _ _) (HR.pts_to hr P.full_perm b');
  HR.pts_to_not_null hr;
  let r : (r: Ghost.erased (ref td) { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) }) = hr in
  vpattern_rewrite (fun hr -> HR.pts_to hr P.full_perm b') r;
  has_array_cell_intro a i r;
  let _ = ghost_array_cell_focus a i r in
  noop ();
  r

[@@ noextract_to "krml"]
let array_cell0
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: ST (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) })
    (array_pts_to a s)
    (fun r -> array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) `star` pts_to r (Seq.index s (SZ.v i)) `star` has_array_cell a i r)
    (
      (SZ.v i < Seq.length s \/ SZ.v i < SZ.v (dsnd a))
    )
    (fun _ -> True)
= array_pts_to_length _ _;
  rewrite (array_pts_to a s) (array_pts_to0 a s);
  let _ = gen_elim () in
  HR.share _;
  rewrite (array_pts_to0 a s) (array_pts_to a s);
  let b = HR.read (dfst a).ar_base in
  vpattern_rewrite (HR.pts_to (dfst a).ar_base _) b;
  let ar = model_array_of_array a b in
  A.ref_of_array_eq ar i;
  let b' = {
    base = b.base;
    ref = R.ref_focus ar.base (A.cell td.pcm ar.base_len (ar.offset `SZ.add`  i));
  }
  in
  let hr = HR.alloc b' in
  HR.pts_to_not_null hr;
  let r : (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) }) = hr in
  vpattern_rewrite (fun hr -> HR.pts_to hr P.full_perm b') r;
  has_array_cell_intro a i r;
  let _ = ghost_array_cell_focus a i r in
  noop ();
  return r

let array_ref_cell
  #_ #td #s a len i
= let r0 : (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd ((| a, len |) <: array td)) }) = array_cell0 _ _ in
  let r : (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v len }) = r0 in
  vpattern_rewrite (fun r -> pts_to r _) r;
  vpattern_rewrite (has_array_cell _ _) r;
  noop ();
  return r

let ar_unfocus_cell
  (#opened: _)
  (#base_t #base_t': Type)
  (#t: Type)
  (#p: pcm t)
  (r: A.array base_t p)
  (s: Seq.seq t)
  (i: SZ.t)
  (r': R.ref base_t' p)
  (v: t)
  (sq: squash (SZ.v i < SZ.v r.len /\ SZ.v i < Seq.length s))
: STGhost unit opened
    (A.pts_to r s `star` R.pts_to r' v)
    (fun _ -> A.pts_to r (Seq.upd s (SZ.v i) v))
    (
      base_t' == base_t /\
      r' == R.ref_focus (A.ref_of_array r) (A.cell p r.len i) /\
      Seq.index s (SZ.v i) == one p
    )
    (fun _ -> True)
= let r1' : R.ref base_t p = coerce_eq () r' in
  rewrite (R.pts_to r' v) (R.pts_to r1' v);
  A.unfocus_cell r s i r1' v ()

let unarray_cell
  #_ #_ #td #s #v a i r
= array_pts_to_length _ _;
  rewrite (array_pts_to a s) (array_pts_to0 a s);
  let _ = gen_elim () in
  let w = has_array_cell_elim a i r in
  let _ = gen_elim () in
  rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  hr_gather (Ghost.reveal w) r;
  ar_unfocus_cell _ _ i _ _ ();
  let b = vpattern_replace (HR.pts_to (dfst a).ar_base _) in
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array a b) (Seq.upd s (SZ.v i) v));
  rewrite (array_pts_to0 a (Seq.upd s (SZ.v i) v)) (array_pts_to a (Seq.upd s (SZ.v i) v));
  has_array_cell_drop _ _ _

#push-options "--split_queries --z3rlimit 16"

let t_array_ref_shift
  (#t: Type)
  (#td: typedef t)
  (a: array_ref td)
  (i: SZ.t)
: Pure (array_ref td)
    (requires (SZ.v (array_ref_offset a) + SZ.v i <= SZ.v (array_ref_base_size a)))
    (ensures (fun y -> 
      array_ref_base_size y == array_ref_base_size a /\
      (forall ty r . has_array_ref_base a #ty r ==> has_array_ref_base y #ty (coerce_eq () r)) /\
      array_ref_offset y == array_ref_offset a `SZ.add` i
    ))
= {
    a with
    ar_offset = a.ar_offset `SZ.add` i
  }

let array_ref_shift
  a i
= t_array_ref_shift a i

let ghost_array_split
  #_ #_ #td #s a i
= array_pts_to_length _ _;
  let sq : squash (SZ.v i <= SZ.v (dsnd a) /\ Seq.length s == SZ.v (dsnd a)) = () in
  rewrite (array_pts_to a s) (array_pts_to0 a s);
  let _ = gen_elim () in
  let br : Ghost.erased (ref0_v (base_array1 td (dfst a).ar_base_size)) = vpattern_replace_erased (HR.pts_to _ _) in
  A.g_split _ _ i ();
  HR.share _;
  let p = vpattern_replace (fun p -> HR.pts_to _ p _ `star` HR.pts_to _ p _) in
  let br_l : Ghost.erased (ref0_v (base_array1 td (dfst (array_split_l a i)).ar_base_size)) = coerce_eq () br in
  rewrite (HR.pts_to _ _ _) (HR.pts_to (dfst (array_split_l a i)).ar_base p br_l);
  rewrite (A.pts_to _ (Seq.slice s 0 _)) (A.pts_to (model_array_of_array (array_split_l a i) br_l) (Seq.slice s 0 (SZ.v i)));
  noop ();
  rewrite (array_pts_to0 (array_split_l a i) (Seq.slice s 0 (SZ.v i))) (array_pts_to (array_split_l a i) (Seq.slice s 0 (SZ.v i)));
  let br_r : Ghost.erased (ref0_v (base_array1 td (dfst (array_split_r a i)).ar_base_size)) = coerce_eq () br in
  rewrite (HR.pts_to _ _ _) (HR.pts_to (dfst (array_split_r a i)).ar_base p br_r);
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array (array_split_r a i) br_r) (Seq.slice s (SZ.v i) (Seq.length s)));
  noop ();
  rewrite (array_pts_to0 (array_split_r a i) (Seq.slice s (SZ.v i) (Seq.length s))) (array_pts_to (array_split_r a i) (Seq.slice s (SZ.v i) (Seq.length s)));
  sq

let t_array_split_r
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
: Pure (array td)
   (requires (SZ.v i <= SZ.v (dsnd a)))
   (ensures (fun _ -> True))
= let (| al, len |) = a in
  (| t_array_ref_shift al i, Ghost.hide (len `SZ.sub` i) |)

let array_ref_split
  #_ #td #s al len i
= let _ = ghost_array_split (| al, len |) i in
  let ar: (ar: array_ref td { SZ.v i <= SZ.v len /\ Seq.length s == SZ.v len}) = t_array_ref_shift al i in
  return ar

let hr_gather_by_perm
  (#opened: _)
  (#t1: Type)
  (#r1: HR.ref t1)
  (#v1: t1)
  (#t2: Type)
  (#r2: HR.ref t2)
  (#v2: t2)
  (p1: P.perm)
  (p2: P.perm)
: STGhost unit opened
    (HR.pts_to r1 p1 v1 `star` HR.pts_to r2 p2 v2)
    (fun _ -> HR.pts_to r1 (p1 `P.sum_perm` p2) v1)
    (t1 == t2 /\
      r1 == r2)
    (fun _ ->
      t1 == t2 /\
      r1 == r2 /\
      v1 == v2)
= rewrite (HR.pts_to r2 p2 v2) (HR.pts_to r1 p2 (coerce_eq () v2));
  HR.gather p2 r1

let ar_join
  (#opened: _)
  (#base_t #base_tl #base_tr: Type)
  (#t: Type)
  (#p: pcm t)
  (a: A.array base_t p)
  (i: SZ.t)
  (al: A.array base_tl p)
  (ar: A.array base_tr p)
  (sl0 sr0: Seq.seq t)
: STGhost unit opened
    (A.pts_to al sl0 `star` A.pts_to ar sr0)
    (fun _ -> A.pts_to a (sl0 `Seq.append` sr0))
    (
      SZ.v i <= SZ.v a.len /\
      base_t == base_tl /\
      base_t == base_tr /\
      al == A.split_l a i /\
      ar == A.split_r a i
    )
    (fun _ -> True)
= let al' : A.array base_t p = coerce_eq () al in
  let ar' : A.array base_t p = coerce_eq () ar in
  rewrite (A.pts_to al sl0) (A.pts_to al' sl0);
  rewrite (A.pts_to ar sr0) (A.pts_to ar' sr0);
  A.join a i al' ar' _ _

let array_join
  #_ #_ #td #sl #sr a al ar i
= rewrite (array_pts_to al sl) (array_pts_to0 al sl);
  let _ = gen_elim () in
  let br_l : ref0_v (base_array1 td (dfst al).ar_base_size) = vpattern_replace (HR.pts_to _ _) in
  let pl = vpattern_replace (fun p -> HR.pts_to _ p _) in
  let br : ref0_v (base_array1 td (dfst a).ar_base_size) = coerce_eq () br_l in
  rewrite (HR.pts_to _ _ _) (HR.pts_to (dfst a).ar_base pl br);
  rewrite (array_pts_to ar sr) (array_pts_to0 ar sr);
  let _ = gen_elim () in
  let pr = vpattern_replace (fun pr -> HR.pts_to _ pl _ `star` HR.pts_to _ pr _) in
  hr_gather_by_perm pl pr;
  ar_join (model_array_of_array a br) i _ _ sl sr;
  rewrite (array_pts_to0 a (sl `Seq.append` sr)) (array_pts_to a (sl `Seq.append` sr))

let ar_share
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: A.array base_t p)
  (s s1 s2: Seq.seq t)
  (prf: (
    (i: nat) ->
    Lemma
    (requires (i < Seq.length s /\ i < Seq.length s1 /\ i < Seq.length s2))
    (ensures (
      i < Seq.length s /\ i < Seq.length s1 /\ i < Seq.length s2 /\
      composable p (Seq.index s1 i) (Seq.index s2 i) /\
      op p (Seq.index s1 i) (Seq.index s2 i) == Seq.index s i
    ))
  ))
: STGhost unit opened
    (A.pts_to r s)
    (fun _ -> A.pts_to r s1 `star` A.pts_to r s2)
    (
      Seq.length s1 == Seq.length s /\
      Seq.length s2 == Seq.length s
    )
    (fun _ -> True)
= Classical.forall_intro (Classical.move_requires prf);
  A.share r s s1 s2

let mk_fraction_seq_split_gen
  #_ #_ #td r v p p1 p2
= rewrite (array_pts_to r (mk_fraction_seq td v p)) (array_pts_to0 r (mk_fraction_seq td v p));
  let _ = gen_elim () in
  let br = vpattern_replace (HR.pts_to _ _) in
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array r br) (mk_fraction_seq td v p));
  ar_share _ _ (mk_fraction_seq td v p1) (mk_fraction_seq td v p2) (fun i ->
    td.mk_fraction_split (Seq.index v i) p1 p2;
    td.mk_fraction_join (Seq.index v i) p1 p2
  );
  HR.share _;
  rewrite (array_pts_to0 r (mk_fraction_seq td v p1)) (array_pts_to r (mk_fraction_seq td v p1));
  rewrite (array_pts_to0 r (mk_fraction_seq td v p2)) (array_pts_to r (mk_fraction_seq td v p2))

let ar_gather
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: A.array base_t p)
  (s s1 s2: Seq.seq t)
  (prf: (
    (i: nat) ->
    Lemma
    (requires (
      i < Seq.length s /\ i < Seq.length s1 /\ i < Seq.length s2 /\
      composable p (Seq.index s1 i) (Seq.index s2 i)
    ))
    (ensures (
      i < Seq.length s /\ i < Seq.length s1 /\ i < Seq.length s2 /\
      composable p (Seq.index s1 i) (Seq.index s2 i) /\
      op p (Seq.index s1 i) (Seq.index s2 i) == Seq.index s i
    ))
  ))
: STGhost unit opened
    (A.pts_to r s1 `star` A.pts_to r s2)
    (fun _ -> A.pts_to r s)
    (
      Seq.length s1 == Seq.length s /\
      Seq.length s2 == Seq.length s
    )
    (fun _ -> True)
= Classical.forall_intro (Classical.move_requires prf);
  A.gather r s s1 s2

let mk_fraction_seq_join
  #_ #_ #td r v p1 p2
= rewrite (array_pts_to r (mk_fraction_seq td v p1)) (array_pts_to0 r (mk_fraction_seq td v p1));
  let _ = gen_elim () in
  let br = vpattern_replace (HR.pts_to _ _) in
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array r br) (mk_fraction_seq td v p1));
  rewrite (array_pts_to r (mk_fraction_seq td v p2)) (array_pts_to0 r (mk_fraction_seq td v p2));
  let _ = gen_elim () in
  hr_gather br (dfst r).ar_base;
  rewrite (A.pts_to _ (mk_fraction_seq _ _ p2)) (A.pts_to (model_array_of_array r br) (mk_fraction_seq td v p2));
  ar_gather _ (mk_fraction_seq td v (p1 `P.sum_perm` p2)) (mk_fraction_seq td v p1) (mk_fraction_seq td v p2) (fun i ->
    td.mk_fraction_join (Seq.index v i) p1 p2
  );
  rewrite (array_pts_to0 r (mk_fraction_seq td v (p1 `P.sum_perm` p2))) (array_pts_to r (mk_fraction_seq td v (p1 `P.sum_perm` p2)))
