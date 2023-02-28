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
module RST = Steel.ST.C.Model.Ref
module ST = Steel.ST.GenElim

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
= ST.exists_ (fun p -> ST.exists_ (fun w ->
    HR.pts_to r p w `star`
    r_pts_to w.ref v
  ))

let _pts_to r v = hp_of (pts_to0 r v)

let pts_to_intro
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (p: P.perm)
  (w1 w2: ref0_v td)
  (v: t)
: ST.STGhost unit opened
    (HR.pts_to r p w1 `star` R.pts_to w2.ref v)
    (fun _ -> pts_to r v)
    (w1 == w2)
    (fun _ -> True)
= ST.vpattern_rewrite (HR.pts_to r p) w2;
  ST.weaken (pts_to0 r v) (pts_to r v) (fun _ -> ())

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
= ST.exists_ (fun p1 -> ST.exists_ (fun p2 -> ST.exists_ (fun w ->
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
: ST.STGhostT unit opened
    (ref_equiv r1 r2)
    (fun _ -> ref_equiv r1 r2 `star` ref_equiv r1 r2)
= ST.rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = ST.gen_elim () in
  HR.share r1;
  HR.share r2;
  ST.rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2);
  ST.noop ();
  ST.rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let ref_equiv_sym'
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: ST.STGhostT unit opened
    (ref_equiv r1 r2)
    (fun _ -> ref_equiv r1 r2 `star` ref_equiv r2 r1)
= ref_equiv_dup' r1 r2;
  ST.rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = ST.gen_elim () in
  ST.noop ();
  ST.rewrite (ref_equiv0 r2 r1) (ref_equiv r2 r1)

let hr_share (#a:Type)
          (#uses:_)
          (#p:P.perm)
          (#v:a)
          (r:HR.ref a)
  : ST.STGhostT unit uses
      (HR.pts_to r p v)
      (fun _ -> HR.pts_to r (P.half_perm p) v `star` HR.pts_to r (P.half_perm p) v)
= HR.share #_ #_ #_ #v r

let hr_gather
  (#a:Type)
  (#uses:_) 
  (#p0 #p1:P.perm)
  (v0 #v1:a)
  (r:HR.ref a)
: ST.STGhost unit uses
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
: ST.STGhostT unit opened
    (ref_equiv r1 r2 `star` ref_equiv r2 r3)
    (fun _ -> ref_equiv r1 r2 `star` ref_equiv r2 r3 `star` ref_equiv r1 r3)
= ST.rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  let p2 = ST.vpattern_replace (fun p -> HR.pts_to r2 p _) in
  ST.rewrite (ref_equiv r2 r3) (ref_equiv0 r2 r3);
  let _ = ST.gen_elim () in
  HR.pts_to_injective_eq #_ #_ #_ #_ #w #_ r2;
  ST.vpattern_rewrite (HR.pts_to r3 _) w;
  hr_share r1;
  hr_share r3;
  HR.gather p2 r2;
  hr_share r2;
  ST.noop ();
  ST.rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2);
  ST.rewrite (ref_equiv0 r2 r3) (ref_equiv r2 r3);
  ST.rewrite (ref_equiv0 r1 r3) (ref_equiv r1 r3)

let hr_share_imbalance (#a:Type)
          (#uses:_)
          (#p:P.perm)
          (#v:a)
          (r:HR.ref a)
  : ST.STGhostT P.perm uses
      (HR.pts_to r p v)
      (fun p1 -> HR.pts_to r p1 v `star` ST.exists_ (fun p2 -> HR.pts_to r p2 v))
= HR.share #_ #_ #_ #v r;
  _

#set-options "--ide_id_info_off"

let pts_to_equiv'
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
  (v: Ghost.erased t)
: ST.STGhostT unit opened
    (ref_equiv r1 r2 `star` pts_to r1 v)
    (fun _ -> ref_equiv r1 r2 `star` pts_to r2 v)
= ST.rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  ST.weaken (pts_to r1 v) (pts_to0 r1 v) (fun _ -> ());
  let _ = ST.gen_elim () in
  hr_gather w r1;
  hr_share r2;
  ST.rewrite (R.pts_to _ _) (R.pts_to w.ref v);
  ST.weaken (pts_to0 r2 v) (pts_to r2 v) (fun _ -> ());
  ST.rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let pts_to_equiv
  r1 r2 v
= pts_to_equiv' r1 r2 v

[@@__steel_reduce__; __reduce__]
let freeable0
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
: Tot vprop
= ST.exists_ (fun p -> ST.exists_ (fun w ->
    HR.pts_to r p w `star`
    ST.pure (R.freeable w.ref)
  ))

let freeable
  r
= freeable0 r

let freeable_dup'
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
: ST.STGhostT unit opened
    (freeable r)
    (fun _ -> freeable r `star` freeable r)
= ST.rewrite (freeable r) (freeable0 r);
  let _ = ST.gen_elim () in
  HR.share r;
  ST.noop ();
  ST.rewrite (freeable0 r) (freeable r);
  ST.noop ();
  ST.rewrite (freeable0 r) (freeable r)

module STC = Steel.ST.Coercions

let freeable_dup
  r
= let _ = freeable_dup' r in
  noop ()

let freeable_equiv'
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: ST.STGhostT unit opened
    (ref_equiv r1 r2 `star` freeable r1)
    (fun _ -> ref_equiv r1 r2 `star` freeable r2)
= ST.rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  ST.rewrite (freeable r1) (freeable0 r1);
  let _ = ST.gen_elim () in
  hr_gather w r1;
  HR.share r2;
  ST.rewrite (freeable0 r2) (freeable r2);
  ST.rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let freeable_equiv
  r1 r2
= freeable_equiv' r1 r2

let alloc'
  (#t: Type)
  (td: typedef t)
: ST.STT (ptr td)
    emp
    (fun p -> pts_to_or_null p (uninitialized td) `star` freeable_or_null p)
= let r = RST.ref_alloc td.pcm td.uninitialized in
  let w = {
    base = _;
    ref = r;
  }
  in
  ST.rewrite (R.pts_to _ _) (R.pts_to w.ref (uninitialized td));
  let res = HR.alloc w in
  HR.share res;
  HR.pts_to_not_null res;
  ST.weaken (pts_to0 res (uninitialized td)) (pts_to_or_null res (uninitialized td)) (fun _ -> ());
  ST.weaken (freeable0 res) (freeable_or_null res) (fun _ -> ());
  ST.return res

let alloc
  td
= alloc' td

let free'
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: ST.ST unit
    (pts_to r v `star` freeable r)
    (fun _ -> emp)
    (
      full td v
    )
    (fun _ -> True)
= ST.weaken (pts_to r v) (pts_to0 r v) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = HR.read r in
  ST.rewrite (R.pts_to _ _) (R.pts_to w.ref v);
  ST.rewrite (freeable r) (freeable0 r);
  let _ = ST.gen_elim () in
  hr_gather w r;
  RST.ref_free w.ref;
  ST.drop (HR.pts_to _ _ _);
  ST.return ()

let free
  r
= free' r

let mk_fraction_split_gen'
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: ref td) (v: t { fractionable td v }) (p p1 p2: P.perm)
: ST.STGhost unit opened
  (pts_to r (mk_fraction td v p))
  (fun _ -> pts_to r (mk_fraction td v p1) `star` pts_to r (mk_fraction td v p2))
  (p == p1 `P.sum_perm` p2 /\ p `P.lesser_equal_perm` P.full_perm)
  (fun _ -> True)
= ST.weaken (pts_to _ _) (pts_to0 r (mk_fraction td v p)) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  td.mk_fraction_split v p1 p2;
  td.mk_fraction_join v p1 p2;
  ST.rewrite
    (R.pts_to _ _)
    (R.pts_to w.ref (op td.pcm (td.mk_fraction v p1) (td.mk_fraction v p2)));
  RST.split _ _ (td.mk_fraction v p1) (td.mk_fraction v p2);
  HR.share r;
  ST.weaken (pts_to0 r (td.mk_fraction v p1)) (pts_to r (mk_fraction td v p1)) (fun _ -> ());
  ST.weaken (pts_to0 r (td.mk_fraction v p2)) (pts_to r (mk_fraction td v p2)) (fun _ -> ())

let mk_fraction_split_gen
  r v p p1 p2
= mk_fraction_split_gen' r v p p1 p2

let mk_fraction_join'
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: ref td) (v: t { fractionable td v }) (p1 p2: P.perm)
: ST.STGhostT unit opened
  (pts_to r (mk_fraction td v p1) `star` pts_to r (mk_fraction td v p2))
  (fun _ -> pts_to r (mk_fraction td v (p1 `P.sum_perm` p2)))
= ST.weaken (pts_to r (mk_fraction td v p1)) (pts_to0 r (mk_fraction td v p1)) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  ST.rewrite (R.pts_to _ _) (R.pts_to w.ref (td.mk_fraction v p1));
  ST.weaken (pts_to r (mk_fraction td v p2)) (pts_to0 r (mk_fraction td v p2)) (fun _ -> ());
  let _ = ST.gen_elim () in
  hr_gather w r;
  ST.rewrite (R.pts_to _ (mk_fraction _ _ p2)) (R.pts_to w.ref (td.mk_fraction v p2));
  let _ = RST.gather w.ref (td.mk_fraction v p1) _ in
  td.mk_fraction_join v p1 p2;
  ST.weaken (pts_to0 r _) (pts_to r _) (fun _ -> ())

let mk_fraction_join
  r v p1 p2
= mk_fraction_join' r v p1 p2

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

let scalar_unique'
  (#opened: _)
  (#t: Type)
  (v1 v2: t)
  (p1 p2: P.perm)
  (r: ref (scalar t))
: ST.STGhost unit opened
    (pts_to r (mk_fraction (scalar t) (mk_scalar v1) p1) `star` pts_to r (mk_fraction (scalar t) (mk_scalar v2) p2))
    (fun _ -> pts_to r (mk_fraction (scalar t) (mk_scalar v1) p1) `star` pts_to r (mk_fraction (scalar t) (mk_scalar v2) p2))
    True
    (fun _ -> v1 == v2 /\ (p1 `P.sum_perm` p2) `P.lesser_equal_perm` P.full_perm)
= ST.weaken (pts_to r (mk_fraction (scalar t) (mk_scalar v1) p1)) (pts_to0 r (Some (Some v1, p1))) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  ST.rewrite (r_pts_to _ (Some (Some v1, p1))) (R.pts_to w.ref (Some (Some v1, p1)));
  ST.weaken (pts_to r _) (pts_to0 r (Some (Some v2, p2))) (fun _ -> ());
  let _ = ST.gen_elim () in
  hr_gather w r;
  ST.rewrite (r_pts_to _ (Some (Some v2, p2))) (R.pts_to w.ref (Some (Some v2, p2)));
  let _ = RST.gather w.ref (Some (Some v1, p1)) (Some (Some v2, p2)) in
  RST.split w.ref _ (Some (Some v1, p1)) (Some (Some v2, p2));
  HR.share r;
  ST.noop (); // FIXME: WHY WHY WHY?
  ST.weaken (pts_to0 r (Some (Some v1, p1))) (pts_to r (mk_fraction (scalar _) (mk_scalar v1) p1)) (fun _ -> ());
  ST.weaken (pts_to0 r (Some (Some v2, p2))) (pts_to r (mk_fraction (scalar _) (mk_scalar v2) p2)) (fun _ -> ())

let scalar_unique
  v1 v2 p1 p2 r0
= scalar_unique' v1 v2 p1 p2 r0

#pop-options

let read0' (#t: Type) (#v: Ghost.erased t) (#p: P.perm) (r: ref (scalar t)) : ST.ST t
  (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
  (fun _ -> pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
  (True)
  (fun v' -> v' == Ghost.reveal v)
= ST.weaken (pts_to r _) (pts_to0 r (Some (Some (Ghost.reveal v), p))) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = HR.read r in
  ST.vpattern_rewrite (HR.pts_to r _) w;
  ST.rewrite (r_pts_to _ _) (R.pts_to w.ref (Some (Some (Ghost.reveal v), p)));
  let v' = RST.ref_read w.ref in
  let Some (Some v0, _) = v' in
  ST.rewrite (R.pts_to _ _) (r_pts_to w.ref (Some (Some (Ghost.reveal v), p)));
  ST.weaken (pts_to0 r (Some (Some (Ghost.reveal v), p))) (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p)) (fun _ -> ());
  ST.return v0

let read0
  r0
= read0' r0

let write' (#t: Type) (#v: Ghost.erased (scalar_t t)) (r: ref (scalar t)) (v': t) : ST.ST unit
  (pts_to r v)
  (fun _ -> pts_to r (mk_fraction (scalar t) (mk_scalar v') P.full_perm))
  (full (scalar t) v)
  (fun _ -> True)
= ST.weaken (pts_to r _) (pts_to0 r (Ghost.reveal v)) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = HR.read r in
  ST.vpattern_rewrite (HR.pts_to r _) w;
  ST.rewrite (r_pts_to _ _) (R.pts_to w.ref (Ghost.reveal v));
  RST.ref_upd w.ref _ _ (R.base_fpu _ _ (Some (Some v', P.full_perm)));
  ST.rewrite (R.pts_to _ _) (r_pts_to w.ref (Some (Some (Ghost.reveal v'), P.full_perm)));
  ST.weaken (pts_to0 r (Some (Some (Ghost.reveal v'), P.full_perm))) (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v')) P.full_perm)) (fun _ -> ())

let write
  r0 v'
= write' r0 v'

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
= ST.exists_ (fun p -> ST.exists_ (fun w -> ST.exists_ (fun p' -> ST.exists_ (fun w' ->
    HR.pts_to r p w `star`
    HR.pts_to r' p' w' `star`
    ST.pure (has_struct_field_gen fields w field w')
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
: ST.STGhostT unit opened
    (has_struct_field1 r field r')
    (fun _ -> has_struct_field1 r field r' `star` has_struct_field1 r field r')
=
  ST.rewrite (has_struct_field1 r field r') (has_struct_field0 r field r');
  let _ = ST.gen_elim () in
  HR.share r;
  HR.share r';
  ST.noop ();
  ST.rewrite (has_struct_field0 r field r') (has_struct_field1 r field r');
  ST.noop ();
  ST.rewrite (has_struct_field0 r field r') (has_struct_field1 r field r')

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
: ST.STGhostT unit opened
    (has_struct_field1 r field r1 `star` has_struct_field1 r field r2)
    (fun _ -> has_struct_field1 r field r1 `star` has_struct_field1 r field r2 `star` ref_equiv r1 r2)
=
  ST.rewrite (has_struct_field1 r field r1) (has_struct_field0 r field r1);
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  let w1 = ST.vpattern_replace (HR.pts_to r1 _) in
  ST.rewrite (has_struct_field1 r field r2) (has_struct_field0 r field r2);
  let _ = ST.gen_elim () in
  hr_gather w r;
  ST.vpattern_rewrite (HR.pts_to r2 _) w1;
  hr_share r;
  hr_share r1;
  ST.rewrite (has_struct_field0 r field r1) (has_struct_field1 r field r1);
  hr_share r2;
  ST.rewrite (has_struct_field0 r field r2) (has_struct_field1 r field r2);
  ST.rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

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
: ST.STGhostT unit opened
    (ref_equiv r1 r2 `star` has_struct_field1 r1 field r')
    (fun _ -> ref_equiv r1 r2 `star` has_struct_field1 r2 field r')
= ST.rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  ST.rewrite (has_struct_field1 r1 field r') (has_struct_field0 r1 field r');
  let _ = ST.gen_elim () in
  hr_gather w r1;
  hr_share r2;
  ST.rewrite (has_struct_field0 r2 field r') (has_struct_field1 r2 field r');
  ST.rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

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
: ST.STGhostT unit opened
    (ref_equiv r1' r2' `star` has_struct_field1 r field r1')
    (fun _ -> ref_equiv r1' r2' `star` has_struct_field1 r field r2')
= ST.rewrite (ref_equiv r1' r2') (ref_equiv0 r1' r2');
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (fun w -> HR.pts_to r1' _ w `star` HR.pts_to r2' _ w) in
  ST.rewrite (has_struct_field1 r field r1') (has_struct_field0 r field r1');
  let _ = ST.gen_elim () in
  hr_gather w r1';
  hr_share r2';
  ST.rewrite (has_struct_field0 r field r2') (has_struct_field1 r field r2');
  ST.rewrite (ref_equiv0 r1' r2') (ref_equiv r1' r2')

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
: ST.STGhostT unit opened
    (has_struct_field1 r field r' `star` pts_to r v)
    (fun _ -> has_struct_field1 r field r' `star` pts_to r (t_struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (t_struct_get_field v field))
= ST.rewrite (has_struct_field1 r field r') (has_struct_field0 r field r');
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  let w' = ST.vpattern_replace (HR.pts_to r' _) in
  ST.weaken (pts_to r v) (pts_to0 r v) (fun _ -> ());
  let _ = ST.gen_elim () in
  hr_gather w r;
  ST.rewrite (r_pts_to _ _) (R.pts_to w.ref (Ghost.reveal v));
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
  RST.split w.ref _ v' vf;
  RST.gfocus w.ref (S.struct_field (struct_field_pcm _) field) vf (t_struct_get_field v field);
  hr_share r;
  hr_share r';
  ST.rewrite (has_struct_field0 r field r') (has_struct_field1 r field r');
  ST.weaken (pts_to0 r v') (pts_to r (t_struct_set_field field (unknown (fields.fd_typedef field)) v)) (fun _ -> ());
  ST.rewrite (R.pts_to _ _) (r_pts_to w'.ref (t_struct_get_field v field));
  ST.weaken (pts_to0 r' (t_struct_get_field v field)) (pts_to r' (t_struct_get_field v field)) (fun _ -> ())
  
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
: ST.STGhostT (Ghost.erased (ref (fields.fd_typedef field))) opened
    (pts_to r v)
    (fun r' -> pts_to r (t_struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (t_struct_get_field v field) `star` has_struct_field1 r field r')
= ST.weaken (pts_to r v) (pts_to0 r v) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  ST.rewrite (r_pts_to _ _) (r_pts_to w.ref (Ghost.reveal v));
  let w' = {
    base = w.base;
    ref = R.ref_focus w.ref (S.struct_field (struct_field_pcm (fields)) field);
  }
  in
  let gr' = GHR.alloc w' in
  let r1' = GHR.reveal_ref gr' in
  GHR.reveal_pts_to gr' P.full_perm w';
  ST.rewrite_equiv (GHR.pts_to _ _ _) (HR.pts_to r1' P.full_perm w');
  HR.pts_to_not_null r1';
  let r' = Ghost.hide r1' in
  ST.rewrite (HR.pts_to r1' P.full_perm w') (HR.pts_to r' P.full_perm w');
  hr_share r;
  ST.rewrite (has_struct_field0 r field r') (has_struct_field1 r field r');
  ST.weaken (pts_to0 r (Ghost.reveal v)) (pts_to r v) (fun _ -> ());
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
: ST.STT (ref (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> pts_to r (t_struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (t_struct_get_field v field) `star` has_struct_field1 r field r')
= ST.weaken (pts_to r v) (pts_to0 r v) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = HR.read r in
  ST.vpattern_rewrite (HR.pts_to r _) w;
  ST.rewrite (r_pts_to _ _) (r_pts_to w.ref (Ghost.reveal v));
  let w' = {
    base = w.base;
    ref = R.ref_focus w.ref (S.struct_field (struct_field_pcm (fields)) field);
  }
  in
  let r' = HR.alloc w' in
  hr_share r;
  ST.rewrite (has_struct_field0 r field r') (has_struct_field1 r field r');
  ST.weaken (pts_to0 r (Ghost.reveal v)) (pts_to r v) (fun _ -> ());
  ghost_struct_field_focus' r field r';
  ST.return r'

let struct_field0
  t' #_ #_ #v r field td'
= let r1' = struct_field' r field in
  let r' : ref td' = r1' in
  ST.rewrite (pts_to r1' _) (pts_to r' (struct_get_field v field));
  ST.rewrite (has_struct_field1 _ _ _) (has_struct_field r field r');
  ST.return r'

let r_unfocus (#opened:_)
  (#ta #ta' #tb #tc: Type)
  (#p: pcm tb)
  (#q: pcm tc)
  (r: R.ref ta q) (r': R.ref ta' p)
  (l: Steel.C.Model.Connection.connection p q) (x: tc)
: ST.STGhost (Ghost.erased tb) opened
    (r `R.pts_to` x)
    (fun x' -> r' `R.pts_to` x')
    (requires
      ta == ta' /\
      r == R.ref_focus r' l)
    (ensures fun x' -> Ghost.reveal x' == l.conn_small_to_large.morph x)
= let r1 : R.ref ta' q = r in
  ST.rewrite (r `R.pts_to` x) (r1 `R.pts_to` x);
  RST.unfocus r1 r' l x;
  let x' = ST.vpattern_replace_erased (R.pts_to r') in
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
: ST.STGhost unit opened
    (has_struct_field1 r field r' `star` pts_to r v `star` pts_to r' v')
    (fun _ -> has_struct_field1 r field r' `star` pts_to r (t_struct_set_field field v' v))
    (
      t_struct_get_field v field == unknown (fields.fd_typedef field)
    )
    (fun _ -> True)
= ST.rewrite (has_struct_field1 r field r') (has_struct_field0 r field r');
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  let w' = ST.vpattern_replace (HR.pts_to r' _) in
  ST.weaken (pts_to r v) (pts_to0 r v) (fun _ -> ());
  let _ = ST.gen_elim () in
  hr_gather w r;
  ST.rewrite (r_pts_to _ (Ghost.reveal v)) (R.pts_to w.ref (Ghost.reveal v));
  ST.weaken (pts_to r' v') (pts_to0 r' v') (fun _ -> ());
  let _ = ST.gen_elim () in
  hr_gather w' r';
  ST.rewrite (r_pts_to _ (Ghost.reveal v')) (R.pts_to w'.ref (Ghost.reveal v'));
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
  let _ = RST.gather w.ref (Ghost.reveal v) _ in
  hr_share r;
  ST.rewrite (has_struct_field0 r field r') (has_struct_field1 r field r');
  ST.weaken (pts_to0 r _) (pts_to r _) (fun _ -> ())

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
= ST.exists_ (fun p -> ST.exists_ (fun w -> ST.exists_ (fun p' -> ST.exists_ (fun w' ->
    HR.pts_to r p w `star`
    HR.pts_to r' p' w' `star`
    ST.pure (has_union_field_gen w field w')
  ))))

let has_union_field
  r field r'
= has_union_field0 r field r'

#push-options "--split_queries"

let has_union_field_dup
  r field r'
= ST.rewrite (has_union_field r field r') (has_union_field0 r field r');
  let _ = ST.gen_elim () in
  hr_share r;
  hr_share r';
  ST.noop ();
  ST.rewrite (has_union_field0 r field r') (has_union_field r field r');
  ST.noop ();
  ST.rewrite (has_union_field0 r field r') (has_union_field r field r')

#push-options "--z3rlimit 16"

let has_union_field_inj
  r field r1 r2
= ST.rewrite (has_union_field r field r1) (has_union_field0 r field r1);
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  ST.rewrite (has_union_field r field r2) (has_union_field0 r field r2);
  let _ = ST.gen_elim () in
  hr_gather w r;
  hr_share r;
  hr_share r1;
  ST.rewrite (has_union_field0 r field r1) (has_union_field r field r1);
  hr_share r2;
  ST.rewrite (has_union_field0 r field r2) (has_union_field r field r2);
  let w' = ST.vpattern_replace (HR.pts_to r1 _) in
  ST.vpattern_rewrite (HR.pts_to r2 _) w';
  ST.rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

#pop-options

let has_union_field_equiv_from
  r1 r2 field r'
= ST.rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  ST.rewrite (has_union_field r1 field r') (has_union_field0 r1 field r');
  let _ = ST.gen_elim () in
  hr_gather w r1;
  hr_share r2;
  ST.rewrite (has_union_field0 r2 field r') (has_union_field r2 field r');
  ST.rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let has_union_field_equiv_to
  r field r1' r2'
= ST.rewrite (ref_equiv r1' r2') (ref_equiv0 r1' r2');
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (fun w -> HR.pts_to r1' _ w `star` HR.pts_to r2' _ w) in
  ST.rewrite (has_union_field r field r1') (has_union_field0 r field r1');
  let _ = ST.gen_elim () in
  hr_gather w r1';
  hr_share r2';
  ST.rewrite (has_union_field0 r field r2') (has_union_field r field r2');
  ST.rewrite (ref_equiv0 r1' r2') (ref_equiv r1' r2')

#push-options "--z3rlimit 16"

#restart-solver

let ghost_union_field_focus
  #_ #tn #_ #n #fields #v r field r'
= ST.rewrite (has_union_field r field r') (has_union_field0 r field r');
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  let w' = ST.vpattern_replace (HR.pts_to r' _) in
  ST.weaken (pts_to r v) (pts_to0 r v) (fun _ -> ());
  let _ = ST.gen_elim () in
  hr_gather w r;
  ST.rewrite (r_pts_to _ _) (R.pts_to w.ref (Ghost.reveal v));
  let v' = U.field_to_union_f (union_field_pcm fields) (Some field) (union_get_field v field) in
  assert (v' `FX.feq` v);
  RST.gfocus w.ref (U.union_field (union_field_pcm fields) (Some field)) v (union_get_field v field);
  ST.rewrite (R.pts_to _ _) (R.pts_to w'.ref (union_get_field v field));
  hr_share r';
  ST.weaken (pts_to0 r' _) (pts_to r' _) (fun _ -> ());
  ST.rewrite (has_union_field0 r field r') (has_union_field r field r')

let ghost_union_field
  #_ #tn #_ #n #fields #v r field
= ST.weaken (pts_to r v) (pts_to0 r v) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  ST.rewrite (r_pts_to _ _) (r_pts_to w.ref (Ghost.reveal v));
  let w' = {
    base = w.base;
    ref = R.ref_focus w.ref (U.union_field (union_field_pcm (fields)) (Some field));
  }
  in
  let gr' = GHR.alloc w' in
  let r1' = GHR.reveal_ref gr' in
  GHR.reveal_pts_to gr' P.full_perm w';
  ST.rewrite_equiv (GHR.pts_to _ _ _) (HR.pts_to r1' P.full_perm w');
  HR.pts_to_not_null r1';
  let r' = Ghost.hide r1' in
  ST.rewrite (HR.pts_to r1' P.full_perm w') (HR.pts_to r' P.full_perm w');
  hr_share r;
  ST.rewrite (has_union_field0 r field r') (has_union_field r field r');
  ST.weaken (pts_to0 r (Ghost.reveal v)) (pts_to r v) (fun _ -> ());
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
: SteelT (ref (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (union_get_field v field))
= ST.weaken (pts_to r v) (pts_to0 r v) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = HR.read r in
  ST.vpattern_rewrite (HR.pts_to r _) w;
  ST.rewrite (r_pts_to _ _) (r_pts_to w.ref (Ghost.reveal v));
  let w' = {
    base = w.base;
    ref = R.ref_focus w.ref (U.union_field (union_field_pcm (fields)) (Some field));
  }
  in
  let r' = HR.alloc w' in
  hr_share r;
  ST.rewrite (has_union_field0 r field r') (has_union_field r field r');
  ST.weaken (pts_to0 r (Ghost.reveal v)) (pts_to r v) (fun _ -> ());
  ghost_union_field_focus r field r';
  ST.return r'

let union_field0
  t' r field td'
=
  let r' = union_field' r field in
  let res : ref td' = r' in
  change_equal_slprop (pts_to r' _) (pts_to res _);
  ST.rewrite (has_union_field r field _) (has_union_field r field res);
  return res

#pop-options


#push-options "--z3rlimit 32"

#restart-solver

let ununion_field
  #_ #tn #_ #n #fields r field #v' r'
= ST.rewrite (has_union_field r field r') (has_union_field0 r field r');
  let _ = ST.gen_elim () in
  let w = ST.vpattern_replace (HR.pts_to r _) in
  let w' = ST.vpattern_replace (HR.pts_to r' _) in
  ST.weaken (pts_to r' v') (pts_to0 r' v') (fun _ -> ());
  let _= ST.gen_elim () in
  hr_gather w' r';
  ST.rewrite (r_pts_to _ _) (R.pts_to w'.ref (Ghost.reveal v'));
  let _ = r_unfocus w'.ref w.ref (coerce_eq () (U.union_field (union_field_pcm fields) (Some field))) _ in
  hr_share r;
  ST.rewrite (has_union_field0 r field r') (has_union_field r field r');
  ST.rewrite (R.pts_to _ _) (R.pts_to w.ref (union_set_field tn n fields field (Ghost.reveal v')));
  ST.admit_ ()

[@@noextract_to "krml"] // primitive
let union_switch_field'
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields)
: Steel (ref (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (uninitialized (fields.fd_typedef field)))
    (fun _ -> full (union0 tn n fields) v)
    (fun _ r' _ -> True)
= ST.weaken (pts_to r v) (pts_to0 r v) (fun _ -> ());
  let _ = ST.gen_elim () in
  let w = HR.read r in
  ST.vpattern_rewrite (HR.pts_to r _) w;
  ST.rewrite (r_pts_to _ _) (R.pts_to w.ref (Ghost.reveal v));
  let v' : union_t0 tn n fields = U.field_to_union_f (union_field_pcm fields) (Some field) (fields.fd_typedef field).uninitialized in
  RST.ref_upd w.ref _ _ (R.base_fpu (union_pcm tn n fields) _ v');
  ST.weaken (pts_to0 r v') (pts_to r v') (fun _ -> ());
  let r' = union_field' r field in
  ST.rewrite (pts_to r' _) (pts_to r' (uninitialized (fields.fd_typedef field)));
  ST.return r'

#pop-options

[@@noextract_to "krml"] // primitive
let union_switch_field1'
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields)
: ST.ST (ref (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (uninitialized (fields.fd_typedef field)))
    (full (union0 tn n fields) v)
    (fun _ -> True)
= STC.coerce_steel (fun _ -> union_switch_field' r field)

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
: ST.ST (ref td') // need to write the pcm carrier value, so this cannot be Ghost or Atomic
    (pts_to r v)
    (fun r' -> has_union_field r field (coerce_eq () r') `star` pts_to r' (Ghost.hide (coerce_eq () (uninitialized (fields.fd_typedef field)))))
    (full (union0 tn n fields) v)
    (fun _ -> True)
= let r' = union_switch_field1' #tn #tf #n #fields #v r field in
  let res : ref td' = r' in
  ST.rewrite (pts_to r' _) (pts_to res (Ghost.hide (coerce_eq () (uninitialized (fields.fd_typedef field)))));
  ST.rewrite (has_union_field r field _) (has_union_field r field (coerce_eq () res));
  ST.return res

let union_switch_field0
  t' r field td'
= union_switch_field0' t' r field td' ()

#pop-options

(*

/// Base arrays (without decay: explicit array types as top-level arrays or struct/union fields of array type)

module A = Steel.C.Model.Array

let base_array_t t _ n = A.array_pcm_carrier t n

[@@noextract_to "krml"] // proof-only
let base_array_fd
  (#t: Type)
  (td: typedef t)
  (n: array_size_t)
: Tot (field_description_gen_t (base_array_index_t n))
= {
    fd_nonempty = (let _ : base_array_index_t n = 0sz in ());
    fd_type = A.array_range t n;
    fd_typedef = (fun _ -> td);
  }

let base_array0 tn td n = struct1 (base_array_fd td n)

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

let has_base_array_cell #_ #_ #n #td r i r' =
  SZ.v i < SZ.v n /\
  has_struct_field_gen (base_array_fd td n) r i r'

let has_base_array_cell_inj
  #_ #_ #_ #n #td r i r1 r2
= has_struct_field_gen_inj (base_array_fd td n) r i r1 r2

/// Array pointers (with decay)

noeq
type array_ref #t td = {
  ar_base_size_token: TD.token;
  ar_base_size: Ghost.erased array_size_t;
  ar_base: ref (base_array0 #t (TD.type_of_token ar_base_size_token) td ar_base_size);
  ar_offset: base_array_index_t ar_base_size;
}
let array_ref_base_size_type ar = TD.type_of_token ar.ar_base_size_token
let array_ref_base_size ar = ar.ar_base_size
let array_ref_base ar = ar.ar_base
let array_ref_offset ar = ar.ar_offset
let array_ref_base_offset_inj a1 a2 =
  TD.type_of_token_inj a1.ar_base_size_token a2.ar_base_size_token

#push-options "--z3rlimit 16"

#restart-solver
let base_array_pcm_eq
  (#t: Type)
  (td: typedef t)
  (n: array_size_t)
  (tn: Type0)
: Lemma
  (A.array_pcm td.pcm n == (base_array0 tn td n).pcm)
  [SMTPat (base_array0 tn td n).pcm]
= pcm0_ext (A.array_pcm td.pcm n) (base_array0 tn td n).pcm
    (fun _ _ -> ())
    (fun x1 x2 ->
      assert (op (A.array_pcm td.pcm n) x1 x2 `FX.feq` op (base_array0 tn td n).pcm x1 x2)
    )
    (fun _ -> ())
    ()

#pop-options

[@@noextract_to "krml"] // proof-only
let coerce (#t1 t2: Type) (x1: t1) : Pure t2
  (requires (t1 == t2))
  (ensures (fun x2 ->
    t1 == t2 /\
    x1 == x2
  ))
= x1

[@@noextract_to "krml"] // proof-only
let model_array_of_array
  (#t: Type)
  (#td: typedef t)
  (a: array td)
: Tot (A.array td.pcm)
= let (| al, len |) = a in
  {
    base_len = Ghost.hide (Ghost.reveal al.ar_base_size);
    base = coerce _ ((Some?.v al.ar_base).ref);
    offset = al.ar_offset;
    len = len;
    prf = ();
  }

let array_pts_to' r v =
  A.pts_to (model_array_of_array r) v

let array_pts_to_length r v =
  rewrite_slprop
    (array_pts_to _ _)
    (A.pts_to (model_array_of_array r) v)
    (fun _ -> ());
  A.pts_to_length _ _;
  rewrite_slprop
    (A.pts_to _ _)
    (array_pts_to _ _)
    (fun _ -> ())

#push-options "--z3rlimit 16"

let ghost_array_of_base_focus
  #_ #tn #_ #n #td #v r a
= let mr : R.ref (A.array_pcm td.pcm n) = coerce _ (Some?.v r).ref in
  let m : A.array td.pcm = {
    base_len = Ghost.hide n;
    base = mr;
    offset = 0sz;
    len = n;
    prf = ();
  }
  in
  rewrite_slprop (pts_to r v) (R.pts_to m.base v) (fun _ -> ());
  assert (seq_of_base_array v `Seq.equal` A.seq_of_array_pcm_carrier v);
  A.array_pcm_carrier_of_seq_of_array_pcm_carrier v;
  A.pts_to_intro_from_base m v (seq_of_base_array v);
  rewrite_slprop (A.pts_to _ _) (array_pts_to _ _) (fun _ -> ())

#pop-options

let ghost_array_of_base
  #_ #tn #_ #n #td #v r
= let tok = TD.get_token tn in
  let ar : array_ref td = {
    ar_base_size_token = tok;
    ar_base_size = Ghost.hide (n <: SZ.t);
    ar_base = r;
    ar_offset = 0sz;
  }
  in
  let res : (a: Ghost.erased (array td)  { has_array_of_base r a }) = Ghost.hide (| ar, Ghost.hide n |) in
  ghost_array_of_base_focus r res;
  res

let array_ref_of_base
  #_ #tn #_ #n #td #v r
= let tok = TD.get_token tn in
  let ar : array_ref td = {
    ar_base_size_token = tok;
    ar_base_size = Ghost.hide (n <: SZ.t);
    ar_base = r;
    ar_offset = 0sz;
  }
  in
  ghost_array_of_base_focus r (| ar, Ghost.hide n |);
  return ar

#push-options "--z3rlimit 16 --split_queries"

#restart-solver
let unarray_of_base
  #t #tn #_ #n #td #v r a
=
  let m = model_array_of_array a in
  rewrite_slprop (array_pts_to _ _) (A.pts_to m v) (fun _ -> ());
  let y : Ghost.erased (A.array_pcm_carrier t m.base_len) = A.pts_to_elim_to_base m v in
  let y' : Ghost.erased (base_array_t t tn n) = Ghost.hide (Ghost.reveal y) in
  rewrite_slprop (R.pts_to m.base y) (pts_to r y') (fun _ -> ());
  y'

#pop-options

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

unfold
let has_base_array_cell0
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: Ghost prop
    (requires True)
    (fun p -> p ==> has_base_array_cell r i r')
= SZ.v i < SZ.v n /\
  has_struct_field_gen (base_array_fd td n) r i r'

#restart-solver
let struct_field_eq_cell
  (#t: Type)
  (td: typedef t)
  (n: array_size_t)
  (k: base_array_index_t n)
: Lemma
  (Steel.C.Model.Struct.struct_field (struct_field_pcm (base_array_fd td n)) k == A.cell td.pcm n k)
= assert_norm (A.array_domain n == base_array_index_t n);
  Steel.C.Model.Struct.struct_field_ext #(A.array_domain n) #(A.array_range t n) (struct_field_pcm (base_array_fd td n)) (A.array_elements_pcm td.pcm n) (fun _ -> ()) k

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

let ghost_array_cell_focus = magic ()

let ghost_array_cell = magic ()
(*
  #_ #_ #_ #s a i
= let ma = model_array_of_array a in
*)

let array_ref_cell = magic ()

let unarray_cell = magic ()

let array_ref_shift = magic ()

let ghost_array_split = magic ()

let array_ref_split = magic ()

let array_join = magic ()

let mk_fraction_seq_split_gen = magic ()

let mk_fraction_seq_join = magic ()
