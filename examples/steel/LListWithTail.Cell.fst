module LListWithTail.Cell

(* A Steel model of C cell structs *)

#push-options "--__no_positivity"
noeq
type mcell (a: Type0) = {
  data: (data: ref a { ~ (is_null data) });
  next: (next: ref (option (mcell a)) { ~ (is_null next) });
}
#pop-options

let ccell_ptrvalue a = option (mcell a)

let ccell_ptrvalue_null a = None

let ccell_ptrvalue_is_null #a x = None? x

let ccell_data #a c =
  (Some?.v c).data

let ccell_next #a c =
  (Some?.v c).next

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
  let pres = Some ({ data = rdata; next = rnext }) in
  let gres = Ghost.hide ({ vcell_data = data; vcell_next = next }) in
  let res = (pres, gres) in
  change_slprop (pts_to rdata full_perm data `star` pts_to rnext full_perm next) (ccell (fst res) full_perm (snd res)) (fun _ -> ());
  res

let next c = c.next
let data c = c.data
let mk_cell n d = {
  next = n;
  data = d
}
