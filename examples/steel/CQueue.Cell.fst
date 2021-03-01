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

#push-options "--ide_id_info_off"

let alloc_cell
  #a data next
=
  let rdata = alloc data in
  change_slprop (pts_to rdata full_perm data `star` emp) (pts_to rdata full_perm data `star` pure (rdata =!= null)) (fun m ->
    pts_to_not_null rdata full_perm data m;
    pure_star_interp (pts_to rdata full_perm data) (rdata =!= null) m
  );
  elim_pure (rdata =!= null);
  let rnext = alloc next in
  change_slprop (pts_to rnext full_perm next `star` emp) (pts_to rnext full_perm next `star` pure (rnext =!= null)) (fun m ->
    pts_to_not_null rnext full_perm next m;
    pure_star_interp (pts_to rnext full_perm next) (rnext =!= null) m
  );
  elim_pure (rnext =!= null);  
  let pres = ({ data = rdata; next = rnext; all_or_none_null = (); }) in
  let gres = Ghost.hide ({ vcell_data = data; vcell_next = next }) in
  let res = (pres, gres) in
  change_slprop (pts_to rdata full_perm data `star` pts_to rnext full_perm next) (ccell (fst res) full_perm (snd res)) (fun _ -> ());
  res

let free_cell
  #a c v
=
  free (ccell_data c);
  free (ccell_next c)
