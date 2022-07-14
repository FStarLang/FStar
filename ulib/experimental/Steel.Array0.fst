module Steel.Array0

/// Definition of the selector and its vprop

let pts_to' // necessary because of the selector return type
  (#elt: Type0) (a: array elt)
  (p: P.perm)
  (s: Seq.lseq elt (length a))
: Tot vprop
= pts_to a p s

let pts_to'_inj
  (#elt: Type0) (a: array elt)
  (p: P.perm)
: Tot (interp_hp_of_injective (pts_to' a p))
= fun x1 x2 m -> pts_to_inj a p x1 p x2 m

// _hp and _sel are declared in the interface so that
// [@@__steel_reduce__] gives users the selector return type by
// normalization. Alternatively, we could define varrayp directly with
// mk_selector_vprop in the interface, but to strengthen the selector
// return type, we would then need to declare pts_to' and pts_to'_inj
// in the interface.

let varrayp_hp a p = mk_selector_vprop_hp (pts_to' a p)
let varrayp_sel a p = mk_selector_vprop_sel _ (pts_to'_inj a p)

let intro_varrayp
  a p s
=
  pts_to_length a _;
  change_equal_slprop
    (pts_to a p s)
    (pts_to' a p s);
  mk_selector_vprop_intro _ (pts_to'_inj a p);
  change_equal_slprop
    (mk_selector_vprop _ _)
    (varrayp a p)

let elim_varrayp
  #_ #elt a p
=
  change_equal_slprop
    (varrayp a p)
    (mk_selector_vprop _ (pts_to'_inj a p));
  let res0 = mk_selector_vprop_elim _ (pts_to'_inj a p) in
  // the following is necessary because the selector return type changed
  let res : Ghost.erased (Seq.seq elt) = Ghost.hide (Ghost.reveal res0) in
  change_equal_slprop
    (pts_to' a p res0)
    (pts_to a p res);
  res
