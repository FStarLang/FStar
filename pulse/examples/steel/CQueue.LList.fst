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

let alloc_cllist
  #a head tail
=
  let rhead = alloc head in
  change_slprop (pts_to rhead full_perm head `star` emp) (pts_to rhead full_perm head `star` pure (rhead =!= null)) (fun m ->
    pts_to_not_null rhead full_perm head m;
    pure_star_interp (pts_to rhead full_perm head) (rhead =!= null) m
  );
  elim_pure (rhead =!= null);
  let rtail = alloc tail in
  change_slprop (pts_to rtail full_perm tail `star` emp) (pts_to rtail full_perm tail `star` pure (rtail =!= null)) (fun m ->
    pts_to_not_null rtail full_perm tail m;
    pure_star_interp (pts_to rtail full_perm tail) (rtail =!= null) m
  );
  elim_pure (rtail =!= null);  
  let pres = ({ head = rhead; tail = rtail; all_or_none_null = (); }) in
  let gres = Ghost.hide ({ vllist_head = head; vllist_tail = tail }) in
  let res = (pres, gres) in
  change_slprop (pts_to rhead full_perm head `star` pts_to rtail full_perm tail) (cllist (fst res) full_perm (snd res)) (fun _ -> ());
  steela_return res
