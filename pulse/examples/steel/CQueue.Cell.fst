module CQueue.Cell

(* A Steel model of C cell structs *)

#push-options "--__no_positivity"
noeq
type mcell (a: Type0) = {
  data: ref a;
  next: ref (mcell a);
  all_or_none_null: squash (is_null data == is_null next);
}
#pop-options

let ccell_ptrvalue a = mcell a

let ccell_ptrvalue_null a = {data = null; next = null; all_or_none_null = ()}

let ccell_ptrvalue_is_null #a x = is_null x.data

let ccell_data #a c =
  c.data

let ccell_next #a c =
  c.next

let vptr_pts_to
  (#opened: _)
  (#a: Type)
  (r: ref a)
: SteelGhost (Ghost.erased a) opened
    (vptr r)
    (fun v -> pts_to r full_perm v)
    (fun _ -> True)
    (fun h v _ -> Ghost.reveal v == h (vptr r))
=
  let v = gget (vptr r) in
  change_slprop
    (vptr r)
    (pts_to r full_perm v)
    v
    (Ghost.hide ())
    (fun m -> ptr_sel_interp r m);
  v

#push-options "--ide_id_info_off"

// FIXME: WHY WHY WHY are the following two SO slow, even with the assumes? (and WHY WHY WHY do they fail without them?)

let ccell_full_ccell
  #opened #a c
=
  let res : Ghost.erased (vcell a) = gget (ccell_full c) in
  elim_vrewrite
    (vptr (ccell_data c) `star` vptr (ccell_next c))
    (ccell_rewrite c);
  reveal_star (vptr (ccell_data c)) (vptr (ccell_next c));
  let vdata : Ghost.erased a = vptr_pts_to (ccell_data c) in
  assert (Ghost.reveal vdata == (Ghost.reveal res).vcell_data);
  assert (vdata == Ghost.hide (Ghost.reveal res).vcell_data);
  let vnext : Ghost.erased (ccell_ptrvalue a) = vptr_pts_to (ccell_next c) in
  assert (Ghost.reveal vnext == (Ghost.reveal res).vcell_next);
  assert (vnext == Ghost.hide (Ghost.reveal res).vcell_next);
(* // wtf congruence?
  assert (
    pts_to (ccell_data c) full_perm vdata ==
    pts_to (ccell_data c) full_perm (Ghost.hide  (Ghost.reveal res).vcell_data)
  );
  assert (
    pts_to (ccell_next c) full_perm vnext ==
    pts_to (ccell_next c) full_perm (Ghost.hide (Ghost.reveal res).vcell_next)
  );
*)
  assume (
    (pts_to (ccell_data c) full_perm vdata `star` pts_to (ccell_next c) full_perm vnext) ==
    (ccell c full_perm res)
  );
  change_equal_slprop
    (pts_to (ccell_data c) full_perm vdata `star` pts_to (ccell_next c) full_perm vnext)
    (ccell c full_perm res);
  res

let alloc_cell_full
  #a data next
=
  let rdata = alloc data in
  let vdata = gget (vptr rdata) in
  assume (Ghost.reveal vdata == data);
  let rnext = alloc next in
  let vnext = gget (vptr rnext) in
  assume (Ghost.reveal vnext == next);
  let res : ccell_lvalue a = ({ data = rdata; next = rnext; all_or_none_null = () }) in
  change_equal_slprop (vptr rdata) (vptr (ccell_data res));
  change_equal_slprop (vptr rnext) (vptr (ccell_next res));
  reveal_star (vptr (ccell_data res)) (vptr (ccell_next res));
  intro_vrewrite (vptr (ccell_data res) `star` vptr (ccell_next res)) (ccell_rewrite res);
  return res

let alloc_cell
  #a data next
=
  let pc = alloc_cell_full data next in
  let vc = ccell_full_ccell pc in
  let res = (pc, vc) in
  change_equal_slprop
    (ccell pc full_perm vc)
    (ccell (fst res) full_perm (snd res));
  return res

let free_cell
  #a c v
=
  free_pt (ccell_data c);
  free_pt (ccell_next c)
