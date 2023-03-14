module Steel.ST.C.Types.Struct.Aux
open Steel.ST.GenElim
friend Steel.ST.C.Types.Base
open Steel.ST.C.Types.Base

open Steel.C.Model.PCM

module P = Steel.FractionalPermission
module R = Steel.ST.C.Model.Ref
module HR = Steel.ST.HigherReference

[@@noextract_to "krml"]
noeq
type field_description_gen_t (field_t: eqtype) : Type u#1 = {
  fd_nonempty: squash (exists (f: field_t) . True);
  fd_type: (field_t -> Type0);
  fd_typedef: ((s: field_t) -> Tot (typedef (fd_type s)));
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

[@@noextract_to "krml"] // proof-only
let t_struct_get_field
  (#field_t: eqtype) (#fields: field_description_gen_t field_t) (s: struct_t1 fields) (f: field_t)
: Tot (fields.fd_type f)
= s f

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
