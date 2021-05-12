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

// TODO: follow CQueue.Cell
let cllist_full_cllist #_ #a c = sladmit ()
let alloc_cllist_full = admit ()

let alloc_cllist
  #a head tail
=
  let rhead = alloc_pt head in
  let rtail = alloc_pt tail in
  let gres = Ghost.hide ({ vllist_head = head; vllist_tail = tail }) in
  let res = ({ head = rhead; tail = rtail; all_or_none_null = (); }, gres) in
  rewrite_slprop (pts_to rhead full_perm head `star` pts_to rtail full_perm tail) (cllist (fst res) full_perm (snd res)) (fun _ -> ());
  return res
