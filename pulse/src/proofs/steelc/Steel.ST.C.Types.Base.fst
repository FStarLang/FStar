module Steel.ST.C.Types.Base

open Steel.C.Model.PCM
open Steel.ST.GenElim1

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
  mk_fraction_full_composable: (
    (v1: t) ->
    (p1: P.perm) ->
    (v2: t) ->
    (p2: P.perm) ->
    Lemma
    (requires (
      exclusive pcm v1 /\ p_refine pcm v1 /\
      exclusive pcm v2 /\ p_refine pcm v2 /\
      fractionable v1 /\ fractionable v2 /\
      composable pcm (mk_fraction v1 p1) (mk_fraction v2 p2)
    ))
    (ensures (
      v1 == v2 /\
      (p1 `P.sum_perm` p2) `P.lesser_equal_perm` P.full_perm
    ))
  );
  extract_full: (
    (x: t) ->
    (x0: Ghost.erased (option (t & P.perm))) ->
    Pure t
      (requires (
        match Ghost.reveal x0 with
        | None -> x == one pcm
        | Some (x1, p) -> exclusive pcm x1 /\ p_refine pcm x1 /\ fractionable x1 /\ compatible pcm (mk_fraction x1 p) x
      ))
      (ensures (fun x' ->
        match Ghost.reveal x0 with
        | None -> x' == one pcm
        | Some (x1, _) -> x' == x1
      ))
  );
}

let fractionable td x = td.fractionable x == true
let mk_fraction td x p = td.mk_fraction x p
let mk_fraction_full td x = td.mk_fraction_full x
let mk_fraction_compose td x p1 p2 = td.mk_fraction_compose x p1 p2

let full td v = exclusive td.pcm v /\ p_refine td.pcm v

let uninitialized td = td.uninitialized

let unknown td = one td.pcm

let full_not_unknown
  td v
= ()

let mk_fraction_unknown td p = td.mk_fraction_one p
let mk_fraction_eq_unknown td v p = td.mk_fraction_eq_one v p

module R = Steel.ST.C.Model.Ref

noeq
type ref0_v : Type u#1 = {
  base: Type0;
  t: Type;
  td: typedef t;
  ref: R.ref base td.pcm;
}

module HR = Steel.ST.HigherReference

let void_ptr = HR.ref ref0_v
let void_null = HR.null

let ptr_gen _ = void_ptr
let null_gen _ = void_null

let ghost_void_ptr_of_ptr_gen x = x
let ghost_ptr_gen_of_void_ptr x _ = x

let ghost_void_ptr_of_ptr_gen_of_void_ptr _ _ = ()
let ghost_ptr_gen_of_void_ptr_of_ptr_gen _ = ()

let r_pts_to
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (r: R.ref a p) (v: b)
: vprop
= R.pts_to r v

let pts_to_cond
  (#t: Type)
  (#td: typedef t)
  (r: ptr td)
  (w: ref0_v)
  (r': R.ref w.base td.pcm)
: GTot prop
=
      t == w.t /\
      td == w.td /\
      r' == w.ref

[@@__reduce__]
let pts_to0
  (#t: Type)
  (#td: typedef t)
  (r: ptr td)
  (v: t)
: Tot vprop
= exists_ (fun p -> exists_ (fun w -> exists_ (fun (r': R.ref w.base td.pcm) ->
    HR.pts_to r p w `star`
    r_pts_to r' v `star`
    pure (pts_to_cond r w r')
  )))

let pts_to r v = pts_to0 r v

let pts_to_intro_precond
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (w: ref0_v)
  (#tbase: Type)
  (r': R.ref tbase td.pcm)
: GTot prop
= tbase == w.base /\
      t == w.t /\
      td == w.td /\
      r' == w.ref

let pts_to_intro
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (p: P.perm)
  (w: ref0_v)
  (#tbase: Type)
  (r': R.ref tbase td.pcm)
  (v: t)
: STGhost unit opened
    (HR.pts_to r p w `star` R.pts_to r' v)
    (fun _ -> pts_to r v)
    (pts_to_intro_precond r w r')
    (fun _ -> True)
= let r2 : R.ref w.base td.pcm = coerce_eq () r' in
  rewrite (R.pts_to r' v) (r_pts_to #w.base #t #td.pcm r2 v);
  intro_pure (pts_to_cond r w r2);
  intro_exists r2 (fun (r': R.ref w.base td.pcm) ->
    HR.pts_to r p w `star`
    r_pts_to r' v `star`
    pure (pts_to_cond r w r')
  );
  rewrite (pts_to0 r v) (pts_to r v)

let is_null
  p
= let res = HR.is_null p in
  return res

let void_ptr_of_ptr
  x
= return x

let ptr_of_void_ptr
  x
= vpattern_rewrite (fun x -> pts_to_or_null x _) x;
  return x

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
  pts_to_intro r2 _ _ _ _;
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
    t = _;
    td = td;
    ref = r;
  }
  in
  let res : ptr td = HR.alloc w in
  HR.share res;
  HR.pts_to_not_null res;
  pts_to_intro res _ _ r _;
  rewrite (pts_to _ _) (pts_to_or_null res (uninitialized td));
  rewrite (freeable0 res) (freeable_or_null res);
  return res

[@@noextract_to "krml"]
let read_ref
  (#t: Type)
  (#td: typedef t)
  (#p: P.perm)
  (#v: Ghost.erased t)
  (#w: Ghost.erased ref0_v)
  (#tbase: Type0)
  (#r': Ghost.erased (R.ref tbase td.pcm))
  (r: ref td)
: ST (R.ref w.base td.pcm)
    (HR.pts_to r p w `star`
      r_pts_to r' v)
    (fun r' -> HR.pts_to r p w `star`
      R.pts_to r' v)
    (tbase == w.base /\
      t == w.t /\
      td == w.td /\
      Ghost.reveal r' == coerce_eq () w.ref
    )
    (fun r' ->
    tbase == w.base /\
      t == w.t /\
      td == w.td /\
      r' == coerce_eq () w.ref
    )
= let w0 = HR.read r in
  let res : R.ref w.base td.pcm = coerce_eq () w0.ref in
  rewrite (r_pts_to _ _) (R.pts_to res v);
  return res

let free
  #_ #_ #v r
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = vpattern_replace_erased (HR.pts_to r _) in
  let r' = read_ref r in
  rewrite (freeable r) (freeable0 r);
  let _ = gen_elim () in
  hr_gather (Ghost.reveal w) r;
  R.ref_free r';
  drop (HR.pts_to _ _ _);
  return ()

let get_ref
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#p: P.perm)
  (#v: t)
  (#w: ref0_v)
  (#tbase: Type0)
  (#r': R.ref tbase td.pcm)
  (r: ref td)
: STGhost (R.ref w.base td.pcm) opened
    (HR.pts_to r p w `star`
      r_pts_to r' v)
    (fun r' -> HR.pts_to r p w `star`
      R.pts_to r' v)
    (tbase == w.base /\
      t == w.t /\
      td == w.td /\
      Ghost.reveal r' == coerce_eq () w.ref
    )
    (fun r' ->
    tbase == w.base /\
      t == w.t /\
      td == w.td /\
      r' == coerce_eq () w.ref
    )
= let res : R.ref w.base td.pcm = coerce_eq () w.ref in
  rewrite (r_pts_to _ _) (R.pts_to res v);
  res

let pts_to_intro_rewrite
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (#p: P.perm)
  (#w: ref0_v)
  (#tbase: Type)
  (r': R.ref tbase td.pcm)
  (#v: t)
  (v': Ghost.erased t)
: STGhost unit opened
    (HR.pts_to r p w `star` R.pts_to r' v)
    (fun _ -> pts_to r v')
    (pts_to_intro_precond r w r' /\
      v == Ghost.reveal v'
    )
    (fun _ -> True)
= pts_to_intro r p w r' v;
  vpattern_rewrite (pts_to r) v'

let mk_fraction_split_gen
  #_ #_ #td r v p p1 p2
= rewrite (pts_to _ _) (pts_to0 r (mk_fraction td v p));
  let _ = gen_elim () in
  let r' = get_ref r in
  td.mk_fraction_split v p1 p2;
  td.mk_fraction_join v p1 p2;
  rewrite
    (R.pts_to _ _)
    (R.pts_to r' (op td.pcm (td.mk_fraction v p1) (td.mk_fraction v p2)));
  R.split _ _ (td.mk_fraction v p1) (td.mk_fraction v p2);
  HR.share r;
  pts_to_intro_rewrite r r' #(td.mk_fraction v p1) (mk_fraction td v p1);
  pts_to_intro_rewrite r r' #(td.mk_fraction v p2) (mk_fraction td v p2)

let mk_fraction_join
  #_ #_ #td r v p1 p2
= rewrite (pts_to r (mk_fraction td v p1)) (pts_to0 r (mk_fraction td v p1));
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let r' = get_ref r in
  rewrite (pts_to r (mk_fraction td v p2)) (pts_to0 r (mk_fraction td v p2));
  let _ = gen_elim () in
  hr_gather w r;
  rewrite (R.pts_to _ (mk_fraction _ _ p2)) (R.pts_to r' (td.mk_fraction v p2));
  let _ = R.gather r' (mk_fraction td v p1) _ in
  td.mk_fraction_join v p1 p2;
  pts_to_intro_rewrite r r' _

let fractional_permissions_theorem
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (v1: t { fractionable td v1 })
  (v2: t { fractionable td v2 })
  (p1 p2: P.perm)
  (r: ref td)
: STGhost unit opened
    (pts_to r (mk_fraction td v1 p1) `star` pts_to r (mk_fraction td v2 p2))
    (fun _ -> pts_to r (mk_fraction td v1 p1) `star` pts_to r (mk_fraction td v2 p2))
    (full td v1 /\ full td v2)
    (fun _ -> v1 == v2 /\ (p1 `P.sum_perm` p2) `P.lesser_equal_perm` P.full_perm)
= rewrite (pts_to r (mk_fraction td v1 p1)) (pts_to0 r (mk_fraction td v1 p1));
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let rr = get_ref r in
  rewrite (pts_to r (mk_fraction td v2 p2)) (pts_to0 r (mk_fraction td v2 p2));
  let _ = gen_elim () in
  hr_gather w r;
  rewrite (R.pts_to _ (mk_fraction td v2 p2)) (R.pts_to rr (mk_fraction td v2 p2));
  let _ = R.gather rr (mk_fraction td v1 p1) (mk_fraction td v2 p2) in
  td.mk_fraction_full_composable v1 p1 v2 p2;
  R.split rr _ (mk_fraction td v1 p1) (mk_fraction td v2 p2);
  hr_share r;
  rewrite (pts_to0 r (mk_fraction td v2 p2)) (pts_to r (mk_fraction td v2 p2));
  rewrite (pts_to0 r (mk_fraction td v1 p1)) (pts_to r (mk_fraction td v1 p1))

let copy
  (#t: Type)
  (#td: typedef t)
  (#v_src: Ghost.erased t { full td v_src /\ fractionable td v_src })
  (#p_src: P.perm)
  (#v_dst: Ghost.erased t { full td v_dst })
  (src: ref td)
  (dst: ref td)
: STT unit
    (pts_to src (mk_fraction td v_src p_src) `star` pts_to dst v_dst)
    (fun _ -> pts_to src (mk_fraction td v_src p_src) `star` pts_to dst v_src)
= 
  rewrite (pts_to src (mk_fraction td v_src p_src)) (pts_to0 src (mk_fraction td v_src p_src));
  let _ = gen_elim () in
  let src' = read_ref src in
  let v_src' = R.ref_read src' in
  let v_dst' = td.extract_full v_src' (Some (Ghost.reveal v_src, p_src)) in
  pts_to_intro src _ _ src' _;
  rewrite (pts_to dst v_dst) (pts_to0 dst v_dst);
  let _ = gen_elim () in
  let dst' = read_ref dst in
  R.ref_upd dst' _ _ (R.base_fpu _ _ v_dst');
  pts_to_intro_rewrite dst dst' _

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

irreducible let norm_field_attr = ()

let has_focus_ref_gen
  (#t1: Type)
  (td1: typedef t1)
  (r: ref0_v)
  (#t2: Type)
  (td2: typedef t2)
  (c: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
  (r': ref0_v)
: GTot prop
= r'.base == r.base /\
  r.t == t1 /\
  r.td == td1 /\
  r'.t == t2 /\
  r'.td == td2 /\
  r'.ref == coerce_eq () (R.ref_focus r.ref c)

[@@__reduce__]
let has_focus_ref0
  (#t1: Type)
  (#td1: typedef t1)
  (p1: ref td1)
  (#t2: Type)
  (#td2: typedef t2)
  (c: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
  (p2: ref td2)
: Tot vprop
= exists_ (fun p -> exists_ (fun w -> exists_ (fun p' -> exists_ (fun w' ->
    HR.pts_to p1 p w `star`
    HR.pts_to p2 p' w' `star`
    pure (has_focus_ref_gen td1 w td2 c w')
  ))))

let has_focus_ref
  (#t1: Type)
  (#td1: typedef t1)
  (p1: ref td1)
  (#t2: Type)
  (#td2: typedef t2)
  (c: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
  (p2: ref td2)
: Tot vprop
= has_focus_ref0 p1 c p2

module GHR = Steel.ST.GhostHigherReference

let ghost_focus_ref
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (#v: Ghost.erased t1)
  (r: ref td1)
  (#t2: Type)
  (td2: typedef t2)
  (c: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
: STGhostT (Ghost.erased (ref td2)) opened
    (pts_to r v)
    (fun r' -> pts_to r v `star` has_focus_ref r c r')
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let rr = get_ref r in
  let w' = {
    base = w.base;
    t = t2;
    td = td2;
    ref = R.ref_focus rr c;
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
  rewrite (has_focus_ref0 r c r') (has_focus_ref r c r');
  pts_to_intro r _ _ rr _;
  r'

[@@noextract_to "krml"] // proof-only
let focus_ref
  (#t1: Type)
  (#td1: typedef t1)
  (#v: Ghost.erased t1)
  (r: ref td1)
  (#t2: Type)
  (td2: typedef t2)
  (c: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
: STT (ref td2)
    (pts_to r v)
    (fun r' -> pts_to r v `star` has_focus_ref r c r')
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = vpattern_replace_erased (HR.pts_to r _) in
  let rr = read_ref r in
  let w' = {
    base = w.base;
    t = t2;
    td = td2;
    ref = R.ref_focus rr c;
  }
  in
  let r' = HR.alloc w' in
  HR.pts_to_not_null r';
  hr_share r;
  rewrite (has_focus_ref0 r c r') (has_focus_ref r c r');
  pts_to_intro r _ _ rr _;
  return r'

let has_focus_ref_dup
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (r: ref td1)
  (#t2: Type)
  (#td2: typedef t2)
  (c: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
  (r': ref td2)
: STGhostT unit opened
    (has_focus_ref r c r')
    (fun _ -> has_focus_ref r c r' `star` has_focus_ref r c r')
=
  rewrite (has_focus_ref r c r') (has_focus_ref0 r c r');
  let _ = gen_elim () in
  HR.share r;
  HR.share r';
  noop ();
  rewrite (has_focus_ref0 r c r') (has_focus_ref r c r');
  noop ();
  rewrite (has_focus_ref0 r c r') (has_focus_ref r c r')

let has_focus_ref_inj
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (r: ref td1)
  (#t2: Type)
  (#td2: typedef t2)
  (c: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
  (r1 r2: ref td2)
: STGhostT unit opened
    (has_focus_ref r c r1 `star` has_focus_ref r c r2)
    (fun _ -> has_focus_ref r c r1 `star` has_focus_ref r c r2 `star` ref_equiv r1 r2)
=
  rewrite (has_focus_ref r c r1) (has_focus_ref0 r c r1);
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let w1 = vpattern_replace (HR.pts_to r1 _) in
  rewrite (has_focus_ref r c r2) (has_focus_ref0 r c r2);
  let _ = gen_elim () in
  hr_gather w r;
  vpattern_rewrite (HR.pts_to r2 _) w1;
  hr_share r;
  hr_share r1;
  rewrite (has_focus_ref0 r c r1) (has_focus_ref r c r1);
  hr_share r2;
  rewrite (has_focus_ref0 r c r2) (has_focus_ref r c r2);
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let has_focus_ref_equiv_from
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (r1: ref td1)
  (#t2: Type)
  (#td2: typedef t2)
  (c: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
  (r': ref td2)
  (r2: ref td1)
: STGhostT unit opened
    (ref_equiv r1 r2 `star` has_focus_ref r1 c r')
    (fun _ -> ref_equiv r1 r2 `star` has_focus_ref r2 c r')
= rewrite (ref_equiv r1 r2) (ref_equiv0 r1 r2);
  let _ = gen_elim () in
  let w = vpattern_replace (fun w -> HR.pts_to r1 _ w `star` HR.pts_to r2 _ w) in
  rewrite (has_focus_ref r1 c r') (has_focus_ref0 r1 c r');
  let _ = gen_elim () in
  hr_gather w r1;
  hr_share r2;
  rewrite (has_focus_ref0 r2 c r') (has_focus_ref r2 c r');
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

let has_focus_ref_equiv_to
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (r: ref td1)
  (#t2: Type)
  (#td2: typedef t2)
  (c: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
  (r1' r2': ref td2)
: STGhostT unit opened
    (ref_equiv r1' r2' `star` has_focus_ref r c r1')
    (fun _ -> ref_equiv r1' r2' `star` has_focus_ref r c r2')
= rewrite (ref_equiv r1' r2') (ref_equiv0 r1' r2');
  let _ = gen_elim () in
  let w = vpattern_replace (fun w -> HR.pts_to r1' _ w `star` HR.pts_to r2' _ w) in
  rewrite (has_focus_ref r c r1') (has_focus_ref0 r c r1');
  let _ = gen_elim () in
  hr_gather w r1';
  hr_share r2';
  rewrite (has_focus_ref0 r c r2') (has_focus_ref r c r2');
  rewrite (ref_equiv0 r1' r2') (ref_equiv r1' r2')

#push-options "--split_queries always"
#restart-solver

let has_focus_ref_id
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (r1: ref td1)
  (r2: ref td1)
: STGhostT unit opened
    (has_focus_ref r1 (Steel.C.Model.Connection.connection_id td1.pcm) r2)
    (fun _ -> has_focus_ref r1 (Steel.C.Model.Connection.connection_id td1.pcm) r2 `star` ref_equiv r1 r2)
= has_focus_ref_dup r1 (Steel.C.Model.Connection.connection_id td1.pcm) r2;
  rewrite (has_focus_ref _ _ _) (has_focus_ref0 r1 (Steel.C.Model.Connection.connection_id td1.pcm) r2);
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r1 _) in
  R.ref_focus_id #w.base #_ #td1.pcm (coerce_eq () w.ref);
  vpattern_rewrite (HR.pts_to r2 _) w;
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

#pop-options

let has_focus_ref_compose
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (r1: ref td1)
  (#t2: Type)
  (#td2: typedef t2)
  (c12: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
  (r2: ref td2)
  (#t3: Type)
  (#td3: typedef t3)
  (c23: Steel.C.Model.Connection.connection td2.pcm td3.pcm)
  (r3: ref td3)
: STGhostT unit opened
    (has_focus_ref r1 c12 r2 `star` has_focus_ref r2 c23 r3)
    (fun _ -> has_focus_ref r1 c12 r2 `star` has_focus_ref r2 c23 r3 `star` has_focus_ref r1 (Steel.C.Model.Connection.connection_compose c12 c23) r3)
= rewrite (has_focus_ref r1 c12 r2) (has_focus_ref0 r1 c12 r2);
  let _ = gen_elim () in
  let w1 = vpattern_replace (HR.pts_to r1 _) in
  let w2 = vpattern_replace (HR.pts_to r2 _) in
  rewrite (has_focus_ref r2 c23 r3) (has_focus_ref0 r2 c23 r3);
  let _ = gen_elim () in
  let w3 = vpattern_replace (HR.pts_to r3 _) in
  hr_gather w2 r2;
  R.ref_focus_comp #_ #_ #_ #_ #td1.pcm #td2.pcm #td3.pcm (coerce_eq () w1.ref <: R.ref w1.base _) c12 c23;
  HR.share r1;
  HR.share r2;
  rewrite (has_focus_ref0 r1 c12 r2) (has_focus_ref r1 c12 r2);
  HR.share r3;
  rewrite (has_focus_ref0 r2 c23 r3) (has_focus_ref r2 c23 r3);
  rewrite (has_focus_ref0 r1 (Steel.C.Model.Connection.connection_compose c12 c23) r3) (has_focus_ref r1 (Steel.C.Model.Connection.connection_compose c12 c23) r3)

module Conn = Steel.C.Model.Connection

let focus_ref_iso
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (#v: Ghost.erased t1)
  (r: ref td1)
  (#t2: Type)
  (#td2: typedef t2)
  (r': ref td2)
  (c: Conn.isomorphism td1.pcm td2.pcm)
: STGhost (Ghost.erased t2) opened
    (pts_to r v `star` has_focus_ref r (Conn.connection_of_isomorphism c) r')
    (fun v' -> pts_to r' v' `star` has_focus_ref r (Conn.connection_of_isomorphism c) r')
    True
    (fun v' -> Ghost.reveal v' == c.iso_1_2.morph v)
= rewrite (has_focus_ref r (Conn.connection_of_isomorphism c) r') (has_focus_ref0 r (Conn.connection_of_isomorphism c) r');
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let w' = vpattern_replace (HR.pts_to r' _) in
  rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let rr = get_ref r in
  hr_gather w r;
  let v' = c.iso_1_2.morph v in
  R.gfocus rr (Conn.connection_of_isomorphism c) v v';
  hr_share r';
  rewrite (has_focus_ref0 r (Conn.connection_of_isomorphism c) r') (has_focus_ref r (Conn.connection_of_isomorphism c) r');
  pts_to_intro r' _ _ _ _;
  _

let unfocus_ref
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (r: ref td1)
  (#t2: Type)
  (#td2: typedef t2)
  (#v': Ghost.erased t2)
  (r': ref td2)
  (c: Steel.C.Model.Connection.connection td1.pcm td2.pcm)
: STGhost (Ghost.erased t1) opened
    (pts_to r' v' `star` has_focus_ref r c r')
    (fun v -> pts_to r v `star` has_focus_ref r c r')
    True
    (fun v -> Ghost.reveal v == c.conn_small_to_large.morph v')
= rewrite (has_focus_ref r c r') (has_focus_ref0 r c r');
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let w' = vpattern_replace (HR.pts_to r' _) in
  rewrite (pts_to r' v') (pts_to0 r' v');
  let _ = gen_elim () in
  hr_gather w' r';
  let rr' = get_ref r' in
  let rr : R.ref w'.base td1.pcm = coerce_eq () w.ref in
  R.unfocus rr' rr c _;
  hr_share r;
  rewrite (has_focus_ref0 r c r') (has_focus_ref r c r');
  pts_to_intro r _ _ _ _;
  _

let has_focus_ref_compose_12_13
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (r1: ref td1)
  (#t2: Type)
  (#td2: typedef t2)
  (c12: Conn.connection td1.pcm td2.pcm)
  (r2: ref td2)
  (#t3: Type)
  (#td3: typedef t3)
  (c23: Conn.connection td2.pcm td3.pcm)
  (r3: ref td3)
: STGhostT unit opened
    (has_focus_ref r1 c12 r2 `star` has_focus_ref r1 (Conn.connection_compose c12 c23) r3)
    (fun _ -> has_focus_ref r1 c12 r2 `star` has_focus_ref r2 c23 r3 `star` has_focus_ref r1 (Conn.connection_compose c12 c23) r3)
= rewrite (has_focus_ref r1 c12 r2) (has_focus_ref0 r1 c12 r2);
  let _ = gen_elim () in
  let w1 = vpattern_replace (HR.pts_to r1 _) in
  let w2 = vpattern_replace (HR.pts_to r2 _) in
  rewrite (has_focus_ref r1 (Conn.connection_compose c12 c23) r3) (has_focus_ref0 r1 (Conn.connection_compose c12 c23) r3);
  let _ = gen_elim () in
  let w3 = vpattern_replace (HR.pts_to r3 _) in
  hr_gather w1 r1;
  R.ref_focus_comp #_ #_ #_ #_ #td1.pcm #td2.pcm #td3.pcm (coerce_eq () w1.ref <: R.ref w1.base _) c12 c23;
  HR.share r1;
  HR.share r2;
  rewrite (has_focus_ref0 r1 c12 r2) (has_focus_ref r1 c12 r2);
  HR.share r3;
  rewrite (has_focus_ref0 r2 c23 r3) (has_focus_ref r2 c23 r3);
  rewrite (has_focus_ref0 r1 (Conn.connection_compose c12 c23) r3) (has_focus_ref r1 (Conn.connection_compose c12 c23) r3)

let ghost_focus_ref_gen
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (#p: P.perm)
  (#w: ref0_v)
  (r: ref td1)
  (#t2: Type)
  (td2: typedef t2)
  (c: Conn.connection td1.pcm td2.pcm)
: STGhost (Ghost.erased (ref td2)) opened
    (HR.pts_to r p w)
    (fun r' -> exists_ (fun p' -> HR.pts_to r p' w `star` has_focus_ref r c r'))
    (t1 == w.t /\
      td1 == w.td
    )
    (fun _ -> True)
= let rr : R.ref w.base td1.pcm = coerce_eq () w.ref in
  let w' = {
    base = w.base;
    t = t2;
    td = td2;
    ref = R.ref_focus rr c;
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
  rewrite (has_focus_ref0 r c r') (has_focus_ref r c r');
  noop ();
  r'

[@@noextract_to "krml"] // proof-only
let focus_ref_gen
  (#t1: Type)
  (#td1: typedef t1)
  (#p: P.perm)
  (#v: Ghost.erased ref0_v)
  (r: ref td1)
  (#t2: Type)
  (td2: typedef t2)
  (c: Conn.connection td1.pcm td2.pcm)
: ST (ref td2)
    (HR.pts_to r p v)
    (fun r' -> exists_ (fun p' -> HR.pts_to r p' v `star` has_focus_ref r c r'))
    (t1 == v.t /\
      td1 == v.td
    )
    (fun _ -> True)
= let w = HR.read r in
  let rr : R.ref w.base td1.pcm = coerce_eq () w.ref in
  let w' = {
    base = w.base;
    t = t2;
    td = td2;
    ref = R.ref_focus rr c;
  }
  in
  let r' = HR.alloc w' in
  HR.pts_to_not_null r';
  hr_share r;
  rewrite (has_focus_ref0 r c r') (has_focus_ref r c r');
  return r'

let ghost_focus_ref_compose_12_13
  (#opened: _)
  (#t1: Type)
  (#td1: typedef t1)
  (r1: ref td1)
  (#t2: Type)
  (td2: typedef t2)
  (c12: Conn.connection td1.pcm td2.pcm)
  (#t3: Type)
  (#td3: typedef t3)
  (c23: Conn.connection td2.pcm td3.pcm)
  (r3: ref td3)
: STGhostT (Ghost.erased (ref td2)) opened
    (has_focus_ref r1 (Conn.connection_compose c12 c23) r3)
    (fun r2 -> has_focus_ref r1 c12 r2 `star` has_focus_ref r2 c23 r3 `star` has_focus_ref r1 (Conn.connection_compose c12 c23) r3)
= rewrite (has_focus_ref r1 (Conn.connection_compose c12 c23) r3) (has_focus_ref0 r1 (Conn.connection_compose c12 c23) r3);
  let _ = gen_elim () in
  let r2 = ghost_focus_ref_gen r1 td2 c12 in
  let _ = gen_elim () in
  rewrite (has_focus_ref0 r1 (Conn.connection_compose c12 c23) r3) (has_focus_ref r1 (Conn.connection_compose c12 c23) r3);
  has_focus_ref_compose_12_13 r1 c12 r2 c23 r3;
  r2

[@@noextract_to "krml"] // proof-only
let focus_ref_compose_12_13
  (#t1: Type)
  (#td1: typedef t1)
  (r1: ref td1)
  (#t2: Type)
  (td2: typedef t2)
  (c12: Conn.connection td1.pcm td2.pcm)
  (#t3: Type)
  (#td3: typedef t3)
  (c23: Conn.connection td2.pcm td3.pcm)
  (r3: ref td3)
: STT (ref td2)
    (has_focus_ref r1 (Conn.connection_compose c12 c23) r3)
    (fun r2 -> has_focus_ref r1 c12 r2 `star` has_focus_ref r2 c23 r3 `star` has_focus_ref r1 (Conn.connection_compose c12 c23) r3)
= rewrite (has_focus_ref r1 (Conn.connection_compose c12 c23) r3) (has_focus_ref0 r1 (Conn.connection_compose c12 c23) r3);
  let _ = gen_elim () in
  let r2 = focus_ref_gen r1 td2 c12 in
  let _ = gen_elim () in
  rewrite (has_focus_ref0 r1 (Conn.connection_compose c12 c23) r3) (has_focus_ref r1 (Conn.connection_compose c12 c23) r3);
  has_focus_ref_compose_12_13 r1 c12 r2 c23 r3;
  return r2
