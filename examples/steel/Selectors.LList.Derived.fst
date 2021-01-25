module Selectors.LList.Derived

let push p x =
  let c = mk_cell p x in
  let head = alloc c in
  intro_llist_cons head p;
  head

let pop #a p =
  let h0 = get #(llist p) () in
  let tl = tail p in
  let x = read p in
  let v = data x in
  free p;
  let h1 = get #(llist tl) () in
  let l = Ghost.hide (v_llist tl h1) in
  change_slprop (llist tl) (llist (Res?.n (Res v tl))) l l (fun _ -> ());
  Res v tl

let rec length #a p =
  if is_null p then (elim_llist_nil p; 0)
  else (
    let tl = tail p in
    let aux = length tl in
    intro_llist_cons p tl;
    1 + aux)
