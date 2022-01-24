module Selectors.LList.Derived

let push p x =
  let c = mk_cell p x in
  let head = malloc c in
  intro_llist_cons head p;
  head


let ind_push r x =
  let h = get #(ind_llist r) () in
  let p = unpack_ind r in
  let c = mk_cell p x in
  let head = malloc c in
  intro_llist_cons head p;
  write r head;
  pack_ind r head

let pop #a p =
  let h0 = get #(llist p) () in
  let tl = tail p in
  let x = read p in
  let v = data x in
  free p;
  let h1 = get #(llist tl) () in
  let l = Ghost.hide (v_llist tl h1) in
  change_slprop (llist tl) (llist (Res?.n (Res v tl))) l l (fun _ -> ());
  return (Res v tl)

let ind_pop r =
  let h = get #(ind_llist r) () in
  let p = unpack_ind r in
  cons_is_not_null p;
  let tl = tail p in
  let x = read p in
  let v = data x in
  free p;
  write r tl;
  pack_ind r tl;
  v

let rec length #a p =
  if is_null p then (elim_llist_nil p; 0)
  else (
    let tl = tail p in
    let aux = length tl in
    intro_llist_cons p tl;
    1 + aux)
