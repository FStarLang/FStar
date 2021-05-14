module CQueue.Cell

(* A Steel model of C cell structs *)

#push-options "--__no_positivity"
noeq
type mcell (a: Type0) = {
  data: ref a;
  next: ref (mcell a);
  all_or_none_null: squash (is_null data == is_null next); // TODO: /\ freeable data /\ freeable next, if freeable is implemented as a pure space proposition rather than as stateful permissions (i.e. "freeable if you have the whole permission")
}
#pop-options

let ccell_ptrvalue a = mcell a

let ccell_ptrvalue_null a = {data = null; next = null; all_or_none_null = ()}

let ccell_ptrvalue_is_null #a x = is_null x.data

let ccell_data #a c =
  c.data

let ccell_next #a c =
  c.next

let ccell0_refine
  (#a: Type0)
  (c: ccell_ptrvalue a)
  (_: t_of emp)
: Tot prop
= ccell_ptrvalue_is_null c == false

// unfold
let ccell0_rewrite
  (#a: Type0)
  (c: ccell_ptrvalue a)
  (_: t_of (emp `vrefine` ccell0_refine c))
: Tot (ccell_lvalue a)
= c

[@@ __steel_reduce__]
let ccell0 (a: Type0) (c: ccell_lvalue a) : Tot vprop =
  (vptr (ccell_data c) `star` vptr (ccell_next c))

// unfold
let ccell_rewrite
  (#a: Type0)
  (c: ccell_ptrvalue a)
  (x: dtuple2 (ccell_lvalue a) (vdep_payload (emp `vrefine` ccell0_refine c `vrewrite` ccell0_rewrite c) (ccell0 a)))
: GTot (vcell a)
= let p =
    dsnd #(ccell_lvalue a) #(vdep_payload (emp `vrefine` ccell0_refine c `vrewrite` ccell0_rewrite c) (ccell0 a)) x
  in
  {
    vcell_data = fst p;
    vcell_next = snd p;
  }

[@@ __steel_reduce__ ; __reduce__] // to avoid manual unfoldings through change_slprop
let ccell1
  (#a: Type0)
  (c: ccell_ptrvalue a)
: Tot vprop
= emp `vrefine` ccell0_refine c `vrewrite` ccell0_rewrite c `vdep` ccell0 a `vrewrite` ccell_rewrite c

let ccell_hp
  #a c
= hp_of (ccell1 c)

let ccell_sel
  #a c
= sel_of (ccell1 c)

let intro_ccell
  #opened #a c
=
  intro_vrefine emp (ccell0_refine c);
  intro_vrewrite (emp `vrefine` ccell0_refine c) (ccell0_rewrite c);
  reveal_star (vptr (ccell_data c)) (vptr (ccell_next c));
  intro_vdep
    (emp `vrefine` ccell0_refine c `vrewrite` ccell0_rewrite c)
    (vptr (ccell_data c) `star` vptr (ccell_next c))
    (ccell0 a);
  intro_vrewrite
    (emp `vrefine` ccell0_refine c `vrewrite` ccell0_rewrite c `vdep` ccell0 a)
    (ccell_rewrite c);
  change_slprop_rel
    (ccell1 c)
    (ccell c)
    (fun x y -> x == y)
    (fun m ->
      assert_norm (hp_of (ccell1 c) == ccell_hp c);
      assert_norm (sel_of (ccell1 c) m === sel_of (ccell c) m)
    )

let elim_ccell_ghost
  #opened #a c
=
  change_slprop_rel
    (ccell c)
    (ccell1 c)
    (fun x y -> x == y)
    (fun m ->
      assert_norm (hp_of (ccell1 c) == ccell_hp c);
      assert_norm (sel_of (ccell1 c) m === sel_of (ccell c) m)
    );
  elim_vrewrite
    (emp `vrefine` ccell0_refine c `vrewrite` ccell0_rewrite c `vdep` ccell0 a)
    (ccell_rewrite c);
  let c' : Ghost.erased (ccell_lvalue a) = elim_vdep
    (emp `vrefine` ccell0_refine c `vrewrite` ccell0_rewrite c)
    (ccell0 a)
  in
  elim_vrewrite (emp `vrefine` ccell0_refine c) (ccell0_rewrite c);
  elim_vrefine emp (ccell0_refine c);
  change_equal_slprop
    (ccell0 a c')
    (vptr (ccell_data (Ghost.reveal c')) `star` vptr (ccell_next (Ghost.reveal c')));
  reveal_star (vptr (ccell_data (Ghost.reveal c'))) (vptr (ccell_next (Ghost.reveal c')));
  c'

let elim_ccell
  #opened #a c
=
  let c2 = elim_ccell_ghost c in
  let c : ccell_lvalue a = c in
  change_equal_slprop (vptr (ccell_data c2)) (vptr (ccell_data c));
  change_equal_slprop (vptr (ccell_next c2)) (vptr (ccell_next c));
  return c

let ccell_not_null
  #opened #a c
=
  let c1 = elim_ccell_ghost c in
  let c2 : ccell_lvalue a = c in
  change_equal_slprop (vptr (ccell_data c1)) (vptr (ccell_data c2));
  change_equal_slprop (vptr (ccell_next c1)) (vptr (ccell_next c2));
  intro_ccell c2;
  change_equal_slprop (ccell c2) (ccell c);
  ()

let freeable _ = True

let ralloc (#a:Type0) (x:a) : Steel (ref a)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> h1 (vptr r) == x /\ not (is_null r))
=
  alloc x

let alloc_cell
  #a data next
=
  let rdata = ralloc data in
  let rnext = ralloc next in
  let res : ccell_lvalue a = ({ data = rdata; next = rnext; all_or_none_null = () }) in
  change_equal_slprop (vptr rdata) (vptr (ccell_data res));
  change_equal_slprop (vptr rnext) (vptr (ccell_next res));
  intro_ccell res;
  return res

let free_cell
  #a c
=
  let c = elim_ccell c in
  free (ccell_data c);
  free (ccell_next c)
