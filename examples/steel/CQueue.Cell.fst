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
  let rdata = alloc_pt data in
  let rnext = alloc_pt next in
  let gres = Ghost.hide ({ vcell_data = data; vcell_next = next }) in
  let res = ({ data = rdata; next = rnext; all_or_none_null = () }, gres) in
  rewrite_slprop (pts_to rdata full_perm data `star` pts_to rnext full_perm next) (ccell (fst res) full_perm (snd res)) (fun _ -> ());
  return res

let free_cell
  #a c v
=
  free_pt (ccell_data c);
  free_pt (ccell_next c)
