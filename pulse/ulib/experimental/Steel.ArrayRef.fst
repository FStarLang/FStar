module Steel.ArrayRef

module A = Steel.Array

let null #a = A.null #a

let is_null r = A.is_null r

let vptr0_refine
  (#a: Type0)
  (r: ref a)
  (s: Seq.lseq a (A.length r))
: Tot prop
= Seq.length s == 1

let vptr0_rewrite
  (#a: Type)
  (r: ref a)
  (p: perm)
  (s: normal (vrefine_t (A.varrayp r p) (vptr0_refine r)))
: Tot a
= Seq.index s 0

[@@__steel_reduce__; __reduce__]
let vptr1
  (#a: Type0)
  (r: ref a)
  (p: perm)
: Tot vprop
= A.varrayp r p `vrefine`
  vptr0_refine r `vrewrite`
  vptr0_rewrite r p

[@@__steel_reduce__]
let vptr0
  (#a: Type0)
  (r: ref a)
  (p: perm)
: Tot vprop
= vptr1 r p

let intro_vptr0
  (#opened: _)
  (#a: Type0)
  (r: ref a)
  (p: perm)
: SteelGhost unit opened
    (A.varrayp r p)
    (fun _ -> vptr0 r p)
    (fun _ -> True)
    (fun h _ h' ->
      let s = A.aselp r p h in
      Seq.length s == 1 /\
      h' (vptr0 r p) == Seq.index s 0
    )
= A.varrayp_not_null r p;
  intro_vrefine (A.varrayp r p) (vptr0_refine r);
  intro_vrewrite (A.varrayp r p `vrefine` vptr0_refine r) (vptr0_rewrite r p);
  change_equal_slprop (vptr1 r p) (vptr0 r p)

let elim_vptr0
  (#opened: _)
  (#a: Type0)
  (r: ref a)
  (p: perm)
: SteelGhost unit opened
    (vptr0 r p)
    (fun _ -> A.varrayp r p)
    (fun _ -> True)
    (fun h _ h' ->
      A.aselp r p h' `Seq.equal` Seq.create 1 (h (vptr0 r p))
    )
=
  change_equal_slprop (vptr0 r p) (vptr1 r p);
  elim_vrewrite (A.varrayp r p `vrefine` vptr0_refine r) (vptr0_rewrite r p);
  elim_vrefine (A.varrayp r p) (vptr0_refine r)

let ptrp r p = hp_of (vptr0 r p)

let ptrp_sel r p = sel_of (vptr0 r p)

let intro_vptrp
  (#opened: _)
  (#a: Type0)
  (r: ref a)
  (p: perm)
: SteelGhost unit opened
    (A.varrayp r p)
    (fun _ -> vptrp r p)
    (fun _ -> True)
    (fun h _ h' ->
      let s = A.aselp r p h in
      Seq.length s == 1 /\
      selp r p h' == Seq.index s 0
    )
= intro_vptr0 r p;
  change_slprop_rel
    (vptr0 r p)
    (vptrp r p)
    (fun v1 v2 -> v1 === v2)
    (fun m ->
      assert (interp (hp_of (vptrp r p)) m);
      assert_norm (sel_of (vptrp r p) m === sel_of (vptr0 r p) m)
    )

let elim_vptrp
  (#opened: _)
  (#a: Type0)
  (r: ref a)
  (p: perm)
: SteelGhost unit opened
    (vptrp r p)
    (fun _ -> A.varrayp r p)
    (fun _ -> True)
    (fun h _ h' ->
      A.aselp r p h' `Seq.equal` Seq.create 1 (selp r p h)
    )
= change_slprop_rel
    (vptrp r p)
    (vptr0 r p)
    (fun v1 v2 -> v1 === v2)
    (fun m ->
      assert (interp (hp_of (vptr0 r p)) m);
      assert_norm (sel_of (vptr0 r p) m === sel_of (vptrp r p) m)
    );
  elim_vptr0 r p

let malloc
  x
= let r = A.malloc x 1sz in
  intro_vptrp r full_perm;
  return r

let free
  r
= elim_vptrp r full_perm;
  A.varrayp_not_null r full_perm;
  A.free r

let readp
  r p
= elim_vptrp r p;
  let res = A.index r 0sz in
  intro_vptrp r p;
  return res

let write
  r x
= elim_vptrp r full_perm;
  A.upd r 0sz x;
  intro_vptrp r full_perm

let share
  #_ #_ #p r
= elim_vptrp r p;
  A.share r p (half_perm p) (half_perm p);
  intro_vptrp r (half_perm p);
  intro_vptrp r (half_perm p)

let gather_gen
  r p0 p1
= elim_vptrp r p0;
  elim_vptrp r p1;
  A.gather r p0 p1;
  let s = sum_perm p0 p1 in
  change_equal_slprop
    (A.varrayp r (sum_perm p0 p1))
    (A.varrayp r s);
  intro_vptrp r s;
  s

let gather
  #_ #_ #p r
= let p' = gather_gen r (half_perm p) (half_perm p) in
  change_equal_slprop
    (vptrp r p')
    (vptrp r p)

let vptrp_not_null
  r p
= elim_vptrp r p;
  A.varrayp_not_null r p;
  intro_vptrp r p
