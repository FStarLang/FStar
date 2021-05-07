module Selectors.LList2

open Steel.FractionalPermission
module Mem = Steel.Memory

#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  tail_fuel: Ghost.erased nat;
  next: ref (cell a);
  data: a;
}
#pop-options

let next #a (c:cell a) : t a = c.next
let data #a (c:cell a) : a = c.data
let mk_cell #a (n: t a) (d:a) = {
  tail_fuel = Ghost.hide 0;
  next = n;
  data = d
}

let null_llist #a = null
let is_null #a ptr = is_null ptr

let v_null_rewrite
  (a: Type0)
  (_: t_of emp)
: Tot (list a)
= []

let v_c
  (n: Ghost.erased nat)
  (#a: Type0)
  (r: t a)
  (c: normal (t_of (vptr r)))
: Tot prop
= (Ghost.reveal c.tail_fuel < Ghost.reveal n) == true // to ensure vprop termination

let v_c_dep
  (n: Ghost.erased nat)
  (#a: Type0)
  (r: t a)
  (nllist: (n': Ghost.erased nat) -> (r: t a  { Ghost.reveal n' < Ghost.reveal n }) -> Pure vprop (requires True) (ensures (fun y -> t_of y == list a)))
  (c: normal (t_of (vrefine (vptr r) (v_c n r))))
: Tot vprop
= nllist c.tail_fuel c.next

let v_c_l_rewrite
  (n: Ghost.erased nat)
  (#a: Type0)
  (r: t a)
  (nllist: (n': Ghost.erased nat) -> (r: t a { Ghost.reveal n' < Ghost.reveal n }) -> Pure vprop (requires True) (ensures (fun y -> t_of y == list a)))
  (res: normal (t_of ((vptr r `vrefine` v_c n r) `vdep` v_c_dep n r nllist)))
: Tot (list a)
= let (| c, l |) = res in
  c.data :: l

let rec nllist
  (a: Type0)
  (n: Ghost.erased nat)
  (r: t a)
: Pure vprop
  (requires True)
  (ensures (fun y -> t_of y == list a))
  (decreases (Ghost.reveal n))
= if is_null r
  then emp `vrewrite` v_null_rewrite a
  else ((vptr r `vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) `vrewrite` v_c_l_rewrite n r (nllist a)

let nllist_eq_not_null
  (a: Type0)
  (n: Ghost.erased nat)
  (r: t a)
: Lemma
  (requires (is_null r == false))
  (ensures (
    nllist a n r == ((vptr r `vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) `vrewrite` v_c_l_rewrite n r (nllist a)
  ))
= assert_norm (nllist a n r ==
    begin if is_null r
    then emp `vrewrite` v_null_rewrite a
    else ((vptr r `vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) `vrewrite` v_c_l_rewrite n r (nllist a)
    end
  )

let llist_vdep
  (#a: Type0)
  (r: t a)
  (c: normal (t_of (vptr r)))
: Tot vprop
= nllist a c.tail_fuel c.next

let llist_vrewrite
  (#a: Type0)
  (r: t a)
  (cl: normal (t_of (vptr r `vdep` llist_vdep r)))
: Tot (list a)
= (dfst cl).data :: dsnd cl

let llist0
  (#a: Type0)
  (r: t a)
: Pure vprop
  (requires True)
  (ensures (fun y -> t_of y == list a))
= if is_null r
  then emp `vrewrite` v_null_rewrite a
  else (vptr r `vdep` llist_vdep r) `vrewrite` llist_vrewrite r

let nllist_of_llist0
  (#a: Type0)
  (r: t a)
: SteelSel (Ghost.erased nat)
    (llist0 r)
    (fun res -> nllist a res r)
    (fun _ -> True)
    (fun h0 res h1 ->
      h0 (llist0 r) == h1 (nllist a res r)
    )
=
  if is_null r
  then begin
    let res = Ghost.hide 0 in
    change_equal_slprop
      (llist0 r)
      (nllist a res r);
    res
  end else begin
    change_equal_slprop
      (llist0 r)
      ((vptr r `vdep` llist_vdep r) `vrewrite` llist_vrewrite r);
    elim_vrewrite (vptr r `vdep` llist_vdep r) (llist_vrewrite r);
    let gk : normal (Ghost.erased (t_of (vptr r))) = elim_vdep (vptr r) (llist_vdep r) in
    let res = Ghost.hide (Ghost.reveal (Ghost.reveal gk).tail_fuel + 1) in
    intro_vrefine (vptr r) (v_c res r);
    intro_vdep
      (vptr r `vrefine` v_c res r)
      (llist_vdep r (Ghost.reveal gk))
      (v_c_dep res r (nllist a));
    intro_vrewrite ((vptr r `vrefine` v_c res r) `vdep` v_c_dep res r (nllist a)) (v_c_l_rewrite res r (nllist a));
    nllist_eq_not_null a res r;
    change_equal_slprop
      (((vptr r `vrefine` v_c res r) `vdep` v_c_dep res r (nllist a)) `vrewrite` v_c_l_rewrite res r (nllist a))
      (nllist a res r);
    res
  end

let llist0_of_nllist
  (#a: Type0)
  (n: Ghost.erased nat)
  (r: t a)
: SteelSel unit
    (nllist a n r)
    (fun _ -> llist0 r)
    (fun _ -> True)
    (fun h0 res h1 ->
      h1 (llist0 r) == h0 (nllist a n r)
    )
=
  if is_null r
  then begin
    change_equal_slprop
      (nllist a n r)
      (llist0 r);
    ()
  end else begin
    nllist_eq_not_null a n r;
    change_equal_slprop
      (nllist a n r)
      (((vptr r `vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) `vrewrite` v_c_l_rewrite n r (nllist a));
    elim_vrewrite ((vptr r `vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) (v_c_l_rewrite n r (nllist a));
    let gk = elim_vdep (vptr r `vrefine` v_c n r) (v_c_dep n r (nllist a)) in
    elim_vrefine (vptr r) (v_c n r);
    intro_vdep
      (vptr r)
      (v_c_dep n r (nllist a) (Ghost.reveal gk))
      (llist_vdep r);
    intro_vrewrite (vptr r `vdep` llist_vdep r) (llist_vrewrite r);
    change_equal_slprop
      ((vptr r `vdep` llist_vdep r) `vrewrite` llist_vrewrite r)
      (llist0 r)
  end

let llist_sl
  #a r
= hp_of (llist0 r)

let llist_sel
  #a r
= fun m -> sel_of (llist0 r) m // eta necessary because sel_of is GTot

let llist_of_llist0
  (#a: Type)
  (r: t a)
: SteelSel unit
    (llist0 r)
    (fun _ -> llist r)
    (fun _ -> True)
    (fun h0 _ h1 -> h1 (llist r) == h0 (llist0 r))
=
  change_slprop_rel
    (llist0 r)
    (llist r)
    (fun x y -> x == y)
    (fun _ -> ())

let llist0_of_llist
  (#a: Type)
  (r: t a)
: SteelSel unit
    (llist r)
    (fun _ -> llist0 r)
    (fun _ -> True)
    (fun h0 _ h1 -> h1 (llist0 r) == h0 (llist r))
=
  change_slprop_rel
    (llist r)
    (llist0 r)
    (fun x y -> x == y)
    (fun _ -> ())

let intro_llist_nil a =
  intro_vrewrite emp (v_null_rewrite a);
  change_equal_slprop
    (emp `vrewrite` v_null_rewrite a)
    (llist0 (null_llist #a));
  llist_of_llist0 (null_llist #a)

let is_nil
  #a ptr
=
  llist0_of_llist ptr;
  let res = is_null ptr in
  if res
  then begin
    change_equal_slprop
      (llist0 ptr)
      (emp `vrewrite` v_null_rewrite a);
    elim_vrewrite emp (v_null_rewrite a);
    intro_vrewrite emp (v_null_rewrite a);
    change_equal_slprop
      (emp `vrewrite` v_null_rewrite a)
      (llist0 ptr)
  end else begin
    change_equal_slprop
      (llist0 ptr)
      ((vptr ptr `vdep` llist_vdep ptr) `vrewrite` llist_vrewrite ptr);
      elim_vrewrite (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr);
      intro_vrewrite (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr);
    change_equal_slprop
      ((vptr ptr `vdep` llist_vdep ptr) `vrewrite` llist_vrewrite ptr)
      (llist0 ptr)
  end;
  llist_of_llist0 ptr;
  res


let intro_llist_cons
  #a ptr1 ptr2
=
  llist0_of_llist ptr2;
  let n = nllist_of_llist0 ptr2 in
  (* set the fuel of the new cons cell *)
  let c = read ptr1 in
  let c' = {c with tail_fuel = n} in
  write ptr1 c' ;
  (* actually cons the cell *)
  vptr_not_null ptr1;
  intro_vdep
    (vptr ptr1)
    (nllist a n ptr2)
    (llist_vdep ptr1);
  intro_vrewrite
    (vptr ptr1 `vdep` llist_vdep ptr1)
    (llist_vrewrite ptr1);
  change_equal_slprop
    ((vptr ptr1 `vdep` llist_vdep ptr1) `vrewrite` llist_vrewrite ptr1)
    (llist0 ptr1);
  llist_of_llist0 ptr1

let tail
  #a ptr
=
  llist0_of_llist ptr;
  change_equal_slprop
    (llist0 ptr)
    ((vptr ptr `vdep` llist_vdep ptr) `vrewrite` llist_vrewrite ptr);
  elim_vrewrite (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr);
  let gc = elim_vdep (vptr ptr) (llist_vdep ptr) in
  (* reset tail fuel to match mk_cell *)
  let c = read ptr in
  let c' = {c with tail_fuel = Ghost.hide 0} in
  write ptr c' ;
  (* actually destruct the list *)
  change_equal_slprop
    (llist_vdep ptr (Ghost.reveal gc))
    (nllist a c.tail_fuel c.next);
  llist0_of_nllist c.tail_fuel c.next;
  llist_of_llist0 c.next;
  c.next
