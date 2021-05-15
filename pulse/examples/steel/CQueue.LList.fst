module CQueue.LList

noeq
type cllist_ptrvalue (a: Type0) = {
  head: ref (ccell_ptrvalue a);
  tail: ref (ref (ccell_ptrvalue a));
  all_or_none_null: squash (is_null head == is_null tail);
}

let cllist_ptrvalue_null a = {head = null; tail = null; all_or_none_null = ()}

let cllist_ptrvalue_is_null #a x = is_null x.head

let cllist_head #a c =
  c.head

let cllist_tail #a c =
  c.tail

#push-options "--ide_id_info_off"

let cllist0_refine
  (#a: Type0)
  (c: cllist_ptrvalue a)
  (_: t_of emp)
: Tot prop
= cllist_ptrvalue_is_null c == false

// unfold
let cllist0_rewrite
  (#a: Type0)
  (c: cllist_ptrvalue a)
  (_: t_of (emp `vrefine` cllist0_refine c))
: Tot (cllist_lvalue a)
= c

[@@ __steel_reduce__]
let cllist0 (a: Type0) (c: cllist_lvalue a) : Tot vprop =
  (vptr (cllist_head c) `star` vptr (cllist_tail c))

// unfold
let cllist_rewrite
  (#a: Type0)
  (c: cllist_ptrvalue a)
  (x: dtuple2 (cllist_lvalue a) (vdep_payload (emp `vrefine` cllist0_refine c `vrewrite` cllist0_rewrite c) (cllist0 a)))
: GTot (vllist a)
= let p =
    dsnd #(cllist_lvalue a) #(vdep_payload (emp `vrefine` cllist0_refine c `vrewrite` cllist0_rewrite c) (cllist0 a)) x
  in
  {
    vllist_head = fst p;
    vllist_tail = snd p;
  }

[@@ __steel_reduce__ ; __reduce__] // to avoid manual unfoldings through change_slprop
let cllist1
  (#a: Type0)
  (c: cllist_ptrvalue a)
: Tot vprop
= emp `vrefine` cllist0_refine c `vrewrite` cllist0_rewrite c `vdep` cllist0 a `vrewrite` cllist_rewrite c

let cllist_hp
  #a c
= hp_of (cllist1 c)

let cllist_sel
  #a c
= sel_of (cllist1 c)

let intro_cllist
  #opened #a c
=
  intro_vrefine emp (cllist0_refine c);
  intro_vrewrite (emp `vrefine` cllist0_refine c) (cllist0_rewrite c);
  reveal_star (vptr (cllist_head c)) (vptr (cllist_tail c));
  intro_vdep
    (emp `vrefine` cllist0_refine c `vrewrite` cllist0_rewrite c)
    (vptr (cllist_head c) `star` vptr (cllist_tail c))
    (cllist0 a);
  intro_vrewrite
    (emp `vrefine` cllist0_refine c `vrewrite` cllist0_rewrite c `vdep` cllist0 a)
    (cllist_rewrite c);
  change_slprop_rel
    (cllist1 c)
    (cllist c)
    (fun x y -> x == y)
    (fun m ->
      assert_norm (hp_of (cllist1 c) == cllist_hp c);
      assert_norm (sel_of (cllist1 c) m === sel_of (cllist c) m)
    )

let elim_cllist_ghost
  #opened #a c
=
  change_slprop_rel
    (cllist c)
    (cllist1 c)
    (fun x y -> x == y)
    (fun m ->
      assert_norm (hp_of (cllist1 c) == cllist_hp c);
      assert_norm (sel_of (cllist1 c) m === sel_of (cllist c) m)
    );
  elim_vrewrite
    (emp `vrefine` cllist0_refine c `vrewrite` cllist0_rewrite c `vdep` cllist0 a)
    (cllist_rewrite c);
  let c' : Ghost.erased (cllist_lvalue a) = elim_vdep
    (emp `vrefine` cllist0_refine c `vrewrite` cllist0_rewrite c)
    (cllist0 a)
  in
  elim_vrewrite (emp `vrefine` cllist0_refine c) (cllist0_rewrite c);
  elim_vrefine emp (cllist0_refine c);
  change_equal_slprop
    (cllist0 a c')
    (vptr (cllist_head (Ghost.reveal c')) `star` vptr (cllist_tail (Ghost.reveal c')));
  reveal_star (vptr (cllist_head (Ghost.reveal c'))) (vptr (cllist_tail (Ghost.reveal c')));
  c'

let elim_cllist
  #opened #a c
=
  let c2 = elim_cllist_ghost c in
  let c : cllist_lvalue a = c in
  change_equal_slprop (vptr (cllist_head c2)) (vptr (cllist_head c));
  change_equal_slprop (vptr (cllist_tail c2)) (vptr (cllist_tail c));
  return c

let cllist_not_null
  #opened #a c
=
  let c1 = elim_cllist_ghost c in
  let c2 : cllist_lvalue a = c in
  change_equal_slprop (vptr (cllist_head c1)) (vptr (cllist_head c2));
  change_equal_slprop (vptr (cllist_tail c1)) (vptr (cllist_tail c2));
  intro_cllist c2;
  change_equal_slprop (cllist c2) (cllist c);
  ()

let freeable _ = True

let ralloc (#a:Type0) (x:a) : Steel (ref a)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> h1 (vptr r) == x /\ not (is_null r))
=
  alloc x

let alloc_llist
  #a head tail
=
  let rhead = ralloc head in
  let rtail = ralloc tail in
  let res : cllist_lvalue a = ({ head = rhead; tail = rtail; all_or_none_null = () }) in
  change_equal_slprop (vptr rhead) (vptr (cllist_head res));
  change_equal_slprop (vptr rtail) (vptr (cllist_tail res));
  intro_cllist res;
  return res

let free_llist
  #a c
=
  let c = elim_cllist c in
  free (cllist_head c);
  free (cllist_tail c)
