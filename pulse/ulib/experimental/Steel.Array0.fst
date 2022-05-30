module Steel.Array0

/// Definition of the selector and its vprop

let pts_to'
  (#elt: Type0) (a: array elt)
  (p: P.perm)
  (s: Seq.lseq elt (length a))
: Tot slprop
= hp_of (pts_to a p s)

let varrayp_hp a p =
  Steel.Memory.h_exists (pts_to' a p)

let varrayp_sel' 
  (#elt: Type) (a: array elt) (p: P.perm)
: Tot (selector' (Seq.lseq elt (length a)) (varrayp_hp a p))
= fun m -> id_elim_exists (pts_to' a p) m

module M = Steel.Memory

let varrayp_sel_depends_only_on
  (#elt: Type)
  (a: array elt)
  (p: P.perm)
  (m0: Steel.Memory.hmem (varrayp_hp a p))
  (m1: mem { disjoint m0 m1 })
: Lemma
  (
    varrayp_sel' a p m0 == varrayp_sel' a p (M.join m0 m1)
  )
  [SMTPat (varrayp_sel' a p (M.join m0 m1))]
= pts_to_inj a p (varrayp_sel' a p m0) p (varrayp_sel' a p (M.join m0 m1)) (M.join m0 m1)

let varrayp_sel_depends_only_on_core
  (#elt: Type)
  (a: array elt)
  (p: P.perm)
  (m0: Steel.Memory.hmem (varrayp_hp a p))
: Lemma
  (
    varrayp_sel' a p m0 == varrayp_sel' a p (core_mem m0)
  )
  [SMTPat (varrayp_sel' a p (core_mem m0))]
= pts_to_inj a p (varrayp_sel' a p m0) p (varrayp_sel' a p (core_mem m0)) m0

let varrayp_sel a p = varrayp_sel' a p

let intro_varrayp
  a p s
=
  pts_to_length a p _;
  change_slprop_rel
    (pts_to a p _)
    (varrayp a p)
    (fun _ s' -> s `Seq.equal` s')
    (fun m ->
      intro_h_exists s (pts_to' a p) m;
      let s' = varrayp_sel' a p m in
      pts_to_inj a p s p s' m
    )

let elim_varrayp
  #_ #elt a p
=
  let s0 = gget (varrayp a p) in
  let refinement (s: Seq.lseq elt (length a)) : Tot prop = s == Ghost.reveal s0 in
  let s1 : Ghost.erased (Seq.seq elt) = Ghost.reveal s0 in
  intro_vrefine (varrayp a p) refinement;
  rewrite_slprop
    (varrayp a p `vrefine` refinement)
    (pts_to a p s1)
    (fun m ->
      interp_vrefine_hp (varrayp a p) refinement m
      // injectivity is not needed, because the return value of the
      // selector is exactly the witness of exists_
    );
  s1
