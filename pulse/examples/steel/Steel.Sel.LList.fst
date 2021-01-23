module Steel.Sel.LList

open Steel.FractionalPermission
module Mem = Steel.Memory
module R = Steel.Reference

friend Steel.SelEffect

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
assume val null_llist (#a:Type) : t a

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
