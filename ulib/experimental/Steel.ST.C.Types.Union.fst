module Steel.ST.C.Types.Union
open Steel.ST.GenElim
friend Steel.ST.C.Types.Base
open Steel.ST.C.Types.Fields
open Steel.ST.C.Types.Scalar

open Steel.C.Model.PCM

module GHR = Steel.ST.GhostHigherReference
module R = Steel.ST.C.Model.Ref
module HR = Steel.ST.HigherReference
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

module FX = FStar.FunctionalExtensionality

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

let has_union_field_gen_inj
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref0_v (union0 tn n fields))
  (field: field_t fields)
  (r1': ref0_v (fields.fd_typedef field))
  (r2': ref0_v (fields.fd_typedef field))
: Lemma
  (requires (has_union_field_gen r field r1' /\ has_union_field_gen r field r2'))
  (ensures (r1' == r2'))
= ()

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

#push-options "--z3rlimit 16"
#restart-solver

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

#pop-options

#push-options "--z3rlimit 64"

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
  let w2' = vpattern_replace (HR.pts_to r2 _) in
  has_union_field_gen_inj w field w' w2';
  vpattern_rewrite (HR.pts_to r2 _) w';
  rewrite (ref_equiv0 r1 r2) (ref_equiv r1 r2)

#pop-options

#push-options "--z3rlimit 32"
#restart-solver

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
