module Steel.ST.C.Types.Base

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

let full_not_unknown
  td v
= ()

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
