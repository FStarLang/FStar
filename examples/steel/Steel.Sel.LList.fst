module Steel.Sel.LList

open Steel.FractionalPermission
module Mem = Steel.Memory
module R = Steel.Reference

// friend Steel.SelEffect

#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  next: ref (cell a);
  data: a;
}
#pop-options

let next (c:cell 'a) : t 'a = c.next
let data (c:cell 'a) : 'a = c.data
let mk_cell (n: t 'a) (d:'a) = {
  next = n;
  data = d
}

(* AF: Need to put that in the standard library at some point *)
let null_llist #a = admit()
let is_null #a ptr = admit()

let rec llist_sl' (#a:Type) (ptr:t a)
                         (l:list (cell a))
    : Tot slprop (decreases l)
    =
    match l with
    | [] ->
      pure (ptr == null_llist)

    | hd :: tl ->
      R.pts_to ptr full_perm hd `Mem.star`
      llist_sl' (next hd) tl `Mem.star`
      pure (ptr =!= null_llist)


let llist_sl ptr = Mem.h_exists (llist_sl' ptr)


let rec datas (#a:Type) (l:list (cell a)) : list a =
  match l with
  | [] -> []
  | hd::tl -> data hd :: datas tl

val llist_sel' (#a:Type0) (ptr:t a) : selector' (list a) (llist_sl ptr)

let llist_sel' #a ptr = fun h ->
  Mem.elim_h_exists (llist_sl' ptr) h;
  let l = FStar.IndefiniteDescription.indefinite_description_ghost (list (cell a))
    (fun x -> interp (llist_sl' ptr x) h) in
  datas l

let llist_sl'_witinv (#a:Type) (ptr:t a) : Lemma (is_witness_invariant (llist_sl' ptr))
  = let rec aux (ptr:t a) (x y:list (cell a)) (m:mem) : Lemma
        (requires interp (llist_sl' ptr x) m /\ interp (llist_sl' ptr y) m)
        (ensures x == y)
        (decreases x)
    = match x with
      | [] -> begin match y with
         | [] -> ()
         | hd::tl ->
           Mem.pure_interp (ptr == null_llist) m;
           Mem.pure_star_interp
             (R.pts_to ptr full_perm hd `Mem.star` llist_sl' (next hd) tl)
             (ptr =!= null_llist) m;
           Mem.pure_interp (ptr =!= null_llist) m

       end
      | hd1::tl1 -> begin match y with
        | [] ->
           Mem.pure_interp (ptr == null_llist) m;
           Mem.pure_star_interp
             (R.pts_to ptr full_perm hd1 `Mem.star` llist_sl' (next hd1) tl1)
             (ptr =!= null_llist) m;
           Mem.pure_interp (ptr =!= null_llist) m
        | hd2::tl2 ->
           R.pts_to_witinv ptr full_perm;
           aux (next hd1) tl1 tl2 m
      end

    in Classical.forall_intro_3 (Classical.move_requires_3 (aux ptr))

let llist_sel_depends_only_on (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (llist_sl ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (llist_sel' ptr m0 == llist_sel' ptr (Mem.join m0 m1))
  = let m':Mem.hmem (llist_sl ptr) = Mem.join m0 m1 in
    Mem.elim_h_exists (llist_sl' ptr) m0;
    Mem.elim_h_exists (llist_sl' ptr) m';
    let l1 = FStar.IndefiniteDescription.indefinite_description_ghost (list (cell a))
      (fun x -> interp (llist_sl' ptr x) m0) in
    let l2 = FStar.IndefiniteDescription.indefinite_description_ghost (list (cell a))
      (fun x -> interp (llist_sl' ptr x) m') in

    llist_sl'_witinv ptr;
    Mem.elim_wi (llist_sl' ptr) l1 l2 m'

let llist_sel_depends_only_on_core (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (llist_sl ptr))
  : Lemma (llist_sel' ptr m0 == llist_sel' ptr (core_mem m0))
  = Mem.elim_h_exists (llist_sl' ptr) m0;
    Mem.elim_h_exists (llist_sl' ptr) (core_mem m0);
    let l1 = FStar.IndefiniteDescription.indefinite_description_ghost (list (cell a))
      (fun x -> interp (llist_sl' ptr x) m0) in
    let l2 = FStar.IndefiniteDescription.indefinite_description_ghost (list (cell a))
      (fun x -> interp (llist_sl' ptr x) (core_mem m0)) in

    llist_sl'_witinv ptr;
    Mem.elim_wi (llist_sl' ptr) l1 l2 (core_mem m0)

let llist_sel #a ptr =
  Classical.forall_intro_2 (llist_sel_depends_only_on ptr);
  Classical.forall_intro (llist_sel_depends_only_on_core ptr);
  llist_sel' ptr


#push-options "--fuel 1 --ifuel 0"

let llist_sel_interp (#a:Type0) (ptr:t a) (l:list (cell a)) (m:mem) : Lemma
  (requires interp (llist_sl' ptr l) m)
  (ensures interp (llist_sl ptr) m /\ llist_sel' ptr m == datas l)
  = intro_h_exists l (llist_sl' ptr) m;
    llist_sl'_witinv ptr

let intro_nil_lemma (a:Type0) (m:mem) : Lemma
    (requires interp (hp_of vemp) m)
    (ensures interp (llist_sl (null_llist #a)) m /\ llist_sel (null_llist #a) m == [])
    = let ptr:t a = null_llist in
      pure_interp (ptr == null_llist) m;
      let open FStar.Tactics in
      assert (llist_sl' ptr [] == pure (ptr == null_llist)) by (norm [delta; zeta; iota]);
      intro_h_exists [] (llist_sl' ptr) m;
      llist_sel_interp ptr [] m

let intro_llist_nil a =
    change_slprop_2 vemp (llist (null_llist #a)) ([] <: list a) (intro_nil_lemma a)

open FStar.Ghost

let intro_cons_lemma_aux (#a:Type0) (ptr1 ptr2:t a)
  (x: cell a) (l:list (cell a)) (m:mem) : Lemma
  (requires interp (R.pts_to ptr1 full_perm x `Mem.star` llist_sl' ptr2 l) m /\
    next x == ptr2)
  (ensures interp (llist_sl' ptr1 (x::l)) m)
  = // AF: Need this as a lemma from standard library: interp (pts_to r) ==> r =!= null
    assume (ptr1 =!= null_llist);
    emp_unit (R.pts_to ptr1 full_perm x `Mem.star` llist_sl' ptr2 l);
    pure_star_interp (R.pts_to ptr1 full_perm x `Mem.star` llist_sl' ptr2 l) (ptr1 =!= null_llist) m

let intro_cons_lemma (#a:Type0) (ptr1 ptr2:t a)
  (x: cell a) (l:list a) (m:mem) : Lemma
  (requires interp (ptr ptr1 `Mem.star` llist_sl ptr2) m /\
    next x == ptr2 /\
    sel_of (vptr ptr1) m == x /\
    sel_of (llist ptr2) m == l)
  (ensures interp (llist_sl ptr1) m /\ llist_sel ptr1 m == data x :: l)
  = Mem.elim_h_exists (llist_sl' ptr2) m;
    let l' = FStar.IndefiniteDescription.indefinite_description_ghost (list (cell a))
      (fun x -> interp (llist_sl' ptr2 x) m) in
    let aux (m:mem) (x:cell a) (ml mr:mem) : Lemma
      (requires disjoint ml mr /\ m == join ml mr /\
        interp (ptr ptr1) ml /\ interp (llist_sl ptr2) mr /\
        ptr_sel ptr1 m == x /\ interp (llist_sl' ptr2 l') m)
      (ensures interp (R.pts_to ptr1 full_perm x `Mem.star` llist_sl' ptr2 l') m)
      = ptr_sel_interp ptr1 ml;
        assert (interp (R.pts_to ptr1 full_perm x) ml);
        Mem.elim_h_exists (llist_sl' ptr2) mr;
        let l2 = FStar.IndefiniteDescription.indefinite_description_ghost (list (cell a))
          (fun x -> interp (llist_sl' ptr2 x) mr) in
        join_commutative ml mr;
        assert (interp (llist_sl' ptr2 l2) m);
        llist_sl'_witinv ptr2;
        assert (interp (llist_sl' ptr2 l') mr);
        intro_star (R.pts_to ptr1 full_perm x) (llist_sl' ptr2 l') ml mr
    in
    elim_star (ptr ptr1) (llist_sl ptr2) m;
    Classical.forall_intro_2 (Classical.move_requires_2 (aux m x));
    assert (interp (R.pts_to ptr1 full_perm x `Mem.star` llist_sl' ptr2 l') m);
    intro_cons_lemma_aux ptr1 ptr2 x l' m;
    intro_h_exists (x::l') (llist_sl' ptr1) m;
    llist_sel_interp ptr1 (x::l') m

let intro_llist_cons ptr1 ptr2 =
  let h = get #(vptr ptr1 `star` llist ptr2) () in
  let x = hide (sel ptr1 h) in
  let l = hide (v_llist ptr2 h) in
  reveal_star (vptr ptr1) (llist ptr2);
  change_slprop (vptr ptr1 `star` llist ptr2) (llist ptr1) (reveal x, reveal l) (data x :: l) (fun m ->  intro_cons_lemma ptr1 ptr2 x l m)


#pop-options
