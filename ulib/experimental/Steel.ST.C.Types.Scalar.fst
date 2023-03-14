module Steel.ST.C.Types.Scalar
open Steel.ST.GenElim
friend Steel.ST.C.Types.Base
open Steel.ST.C.Types.Base

open Steel.C.Model.PCM

module R = Steel.ST.C.Model.Ref
module HR = Steel.ST.HigherReference
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

#set-options "--smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native" // for mk_fraction_split

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
