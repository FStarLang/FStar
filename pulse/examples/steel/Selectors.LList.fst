module Selectors.LList

open FStar.Ghost
open Steel.FractionalPermission
module Mem = Steel.Memory
module R = Steel.Reference
open Steel.SelEffect.Atomic
open Steel.SelEffect

#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  next: ref (cell a);
  data: a;
}
#pop-options

let next #a (c:cell a) : t a = c.next
let data #a (c:cell a) : a = c.data
let mk_cell #a (n: t a) (d:a) = {
  next = n;
  data = d
}

(* AF: Need to put that in the standard library at some point *)
let null_llist #a = R.null
let is_null #a ptr = R.is_null ptr

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

val llist_sel_cell' (#a:Type0) (ptr:t a) : selector' (list (cell a)) (llist_sl ptr)

let llist_sel_cell' #a ptr = fun h -> id_elim_exists (llist_sl' ptr) h

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
  : Lemma (llist_sel_cell' ptr m0 == llist_sel_cell' ptr (Mem.join m0 m1))
  = let m':Mem.hmem (llist_sl ptr) = Mem.join m0 m1 in
    let l1 = Ghost.reveal (id_elim_exists (llist_sl' ptr) m0) in
    let l2 = Ghost.reveal (id_elim_exists (llist_sl' ptr) m') in

    llist_sl'_witinv ptr;
    Mem.elim_wi (llist_sl' ptr) l1 l2 m'

let llist_sel_depends_only_on_core (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (llist_sl ptr))
  : Lemma (llist_sel_cell' ptr m0 == llist_sel_cell' ptr (core_mem m0))
  = let l1 = Ghost.reveal (id_elim_exists (llist_sl' ptr) m0) in
    let l2 = Ghost.reveal (id_elim_exists (llist_sl' ptr) (core_mem m0)) in
    llist_sl'_witinv ptr;
    Mem.elim_wi (llist_sl' ptr) l1 l2 (core_mem m0)

val llist_sel_cell (#a:Type0) (r:t a) : selector (list (cell a)) (llist_sl r)

let llist_sel_cell #a ptr =
  Classical.forall_intro_2 (llist_sel_depends_only_on ptr);
  Classical.forall_intro (llist_sel_depends_only_on_core ptr);
  llist_sel_cell' ptr


let llist_sel ptr = fun h -> datas (llist_sel_cell ptr h)

#push-options "--fuel 1 --ifuel 1"

let llist_sel_interp (#a:Type0) (ptr:t a) (l:list (cell a)) (m:mem) : Lemma
  (requires interp (llist_sl' ptr l) m)
  (ensures interp (llist_sl ptr) m /\ llist_sel_cell' ptr m == l)
  = intro_h_exists l (llist_sl' ptr) m;
    llist_sl'_witinv ptr

let intro_nil_lemma (a:Type0) (m:mem) : Lemma
    (requires interp (hp_of vemp) m)
    (ensures interp (llist_sl (null_llist #a)) m /\ llist_sel (null_llist #a) m == [])
    = let ptr:t a = null_llist in
      pure_interp (ptr == null_llist) m;
      let open FStar.Tactics in
      assert (llist_sl' ptr [] == pure (ptr == null_llist)) by (norm [delta; zeta; iota]);
      llist_sel_interp ptr [] m

let intro_llist_nil a =
    change_slprop_2 vemp (llist (null_llist #a)) ([] <: list a) (intro_nil_lemma a)

let elim_nil_lemma (#a:Type0) (ptr:t a) (m:mem) : Lemma
    (requires interp (llist_sl ptr) m /\ ptr == null_llist)
    (ensures interp (llist_sl ptr) m /\ llist_sel ptr m == [])
    = let l' = id_elim_exists (llist_sl' ptr) m in
      pure_interp (ptr == null_llist) m;
      llist_sel_interp ptr [] m

let elim_llist_nil #a ptr =
  change_slprop_rel (llist ptr) (llist ptr)
    (fun x y -> x == y /\ y == [])
    (fun m -> elim_nil_lemma ptr m)

#set-options "--z3rlimit 20"

let lemma_cons_not_null (#a:Type) (ptr:t a) (l:list a) (m:mem) : Lemma
    (requires interp (llist_sl ptr) m /\ llist_sel ptr m == l /\ Cons? l)
    (ensures ptr =!= null_llist)
    = let l' = id_elim_exists (llist_sl' ptr) m in
      assert (interp (llist_sl' ptr l') m);
      llist_sel_interp ptr l' m;
      match reveal l' with
      | hd::tl ->
          let p = R.pts_to ptr full_perm (hide hd) `Mem.star` llist_sl' (next hd) tl in
          pure_star_interp p (ptr =!= null_llist) m

let cons_is_not_null #a ptr =
  let h = get () in
  let l = hide (v_llist ptr h) in
  extract_info (llist ptr) l (ptr =!= null_llist) (lemma_cons_not_null ptr l)

let intro_cons_lemma_aux (#a:Type0) (ptr1 ptr2:t a)
  (x: cell a) (l:list (cell a)) (m:mem) : Lemma
  (requires interp (R.pts_to ptr1 full_perm x `Mem.star` llist_sl' ptr2 l) m /\
    next x == ptr2)
  (ensures interp (llist_sl' ptr1 (x::l)) m)
  = affine_star (R.pts_to ptr1 full_perm x) (llist_sl' ptr2 l) m;
    R.pts_to_not_null ptr1 full_perm x m;
    emp_unit (R.pts_to ptr1 full_perm x `Mem.star` llist_sl' ptr2 l);
    pure_star_interp
      (R.pts_to ptr1 full_perm x `Mem.star` llist_sl' ptr2 l)
      (ptr1 =!= null_llist)
      m

let intro_cons_lemma (#a:Type0) (ptr1 ptr2:t a)
  (x: cell a) (l:list a) (m:mem) : Lemma
  (requires interp (ptr ptr1 `Mem.star` llist_sl ptr2) m /\
    next x == ptr2 /\
    sel_of (vptr ptr1) m == x /\
    sel_of (llist ptr2) m == l)
  (ensures interp (llist_sl ptr1) m /\ llist_sel ptr1 m == data x :: l)
  = let l' = id_elim_exists (llist_sl' ptr2) m in
    let aux (m:mem) (x:cell a) (ml mr:mem) : Lemma
      (requires disjoint ml mr /\ m == join ml mr /\
        interp (ptr ptr1) ml /\ interp (llist_sl ptr2) mr /\
        ptr_sel ptr1 m == x /\ interp (llist_sl' ptr2 l') m)
      (ensures interp (R.pts_to ptr1 full_perm x `Mem.star` llist_sl' ptr2 l') m)
      = ptr_sel_interp ptr1 ml;
        assert (interp (R.pts_to ptr1 full_perm x) ml);
        let l2 = id_elim_exists (llist_sl' ptr2) mr in
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
  let h = get () in
  let x = hide (sel ptr1 h) in
  let l = hide (v_llist ptr2 h) in
  reveal_star (vptr ptr1) (llist ptr2);
  change_slprop (vptr ptr1 `star` llist ptr2) (llist ptr1) (reveal x, reveal l) (data x :: l) (fun m ->  intro_cons_lemma ptr1 ptr2 x l m)

let reveal_non_empty_lemma (#a:Type) (ptr:t a) (l:list (cell a)) (m:mem) : Lemma
    (requires interp (llist_sl ptr) m /\ llist_sel_cell ptr m == l /\ ptr =!= null_llist)
    (ensures Cons? l)
= let l' = id_elim_exists (llist_sl' ptr) m in
  llist_sel_interp ptr l' m;
  pure_interp (ptr == null_llist) m

let is_cons (#a:Type) (l:list a) : prop = match l with
  | [] -> False
  | _ -> True

[@@__steel_reduce__]
let llist_cell' #a r : vprop' =
  {hp = llist_sl r;
   t = list (cell a);
   sel = llist_sel_cell r}
unfold
let llist_cell (#a:Type0) (r:t a) = VUnit (llist_cell' r)

[@@ __steel_reduce__]
let v_cell (#a:Type0) (#p:vprop) (r:t a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (llist_cell r) /\ True)}) : GTot (list (cell a))
  = h (llist_cell r)

val reveal_non_empty_cell (#a:Type0) (ptr:t a)
  : SteelSel unit (llist_cell ptr) (fun _ -> llist_cell ptr)
             (requires fun _ -> ptr =!= null_llist)
             (ensures fun h0 _ h1 -> v_cell ptr h0 == v_cell ptr h1 /\ Cons? (v_cell ptr h0))

let reveal_non_empty_cell #a ptr =
  let h = get () in
  let l = hide (v_cell ptr h) in
  extract_info (llist_cell ptr) l (is_cons l) (reveal_non_empty_lemma ptr l)

let tail_cell_lemma (#a:Type0) (r:t a) (l:list (cell a)) (m:mem) : Lemma
  (requires Cons? l /\ interp (llist_sl r) m /\ llist_sel_cell r m == l)
  (ensures (let x = L.hd l in
    interp (ptr r `Mem.star` llist_sl (next x)) m /\
    sel_of (vptr r) m == x /\
    sel_of (llist_cell (next x)) m == L.tl l))
  = llist_sel_interp r l m;
    assert (interp (llist_sl' r l) m);
    let x = L.hd l in
    let tl = L.tl l in
    let sl = R.pts_to r full_perm x `Mem.star` llist_sl' (next x) tl in
    pure_star_interp sl (r =!= null_llist) m;
    emp_unit sl;
    assert (interp sl m);
    let aux (m:mem) (ml mr:mem) : Lemma
      (requires disjoint ml mr /\ m == join ml mr /\
        interp (R.pts_to r full_perm x) ml /\ interp (llist_sl' (next x) tl) mr)
      (ensures interp (ptr r `Mem.star` llist_sl (next x)) m /\
        sel_of (vptr r) m == x /\
        sel_of (llist_cell (next x)) m == tl)
      = intro_h_exists (hide x) (R.pts_to r full_perm) ml;
        llist_sel_interp (next x) tl mr;
        intro_star (ptr r) (llist_sl (next x)) ml mr;
        ptr_sel_interp r ml;
        R.pts_to_witinv r full_perm;
        join_commutative ml mr
    in
    elim_star (R.pts_to r full_perm x) (llist_sl' (next x) tl) m;
    Classical.forall_intro_2 (Classical.move_requires_2 (aux m))


val tail_cell (#a:Type0) (ptr:t a)
  : SteelSel (t a) (llist_cell ptr)
                   (fun n -> vptr ptr `star` llist_cell n)
                   (requires fun _ -> ptr =!= null_llist)
                   (ensures fun h0 n h1 ->
                     Cons? (v_cell ptr h0) /\
                     n == next (sel ptr h1) /\
                     sel ptr h1 == L.hd (v_cell ptr h0) /\
                     v_cell n h1 == L.tl (v_cell ptr h0))

let tail_cell #a ptr =
  let h = get () in
  let l = hide (v_cell ptr h) in
  reveal_non_empty_cell ptr;
  let x = hide (L.hd l) in
  change_slprop (llist_cell ptr) (vptr ptr `star` llist_cell (next x)) l (reveal x, L.tl l)
    (fun m -> tail_cell_lemma ptr l m);
  reveal_star (vptr ptr) (llist_cell (next x));
  let v = read ptr in
  change_slprop (llist_cell (next x)) (llist_cell (next v)) (L.tl l) (L.tl l) (fun _ -> ());
  return (next v)

val to_list_cell (#a:Type0) (ptr:t a)
  : SteelSel unit (llist ptr) (fun _ -> llist_cell ptr)
                  (requires fun _ -> True)
                  (ensures fun h0 _ h1 -> v_llist ptr h0 == datas (v_cell ptr h1))

let to_list_cell ptr =
  change_slprop_rel (llist ptr) (llist_cell ptr) (fun x y -> x == datas y) (fun _ -> ())

val from_list_cell (#a:Type0) (ptr:t a)
  : SteelSel unit (llist_cell ptr) (fun _ -> llist ptr)
                  (requires fun _ -> True)
                  (ensures fun h0 _ h1 -> v_llist ptr h1 == datas (v_cell ptr h0))

let from_list_cell ptr =
  change_slprop_rel (llist_cell ptr) (llist ptr) (fun x y -> datas x == y) (fun _ -> ())

let tail #a ptr =
  // AF: Not sure why these gets are needed for verification?
  let h0 = get () in
  to_list_cell ptr;
  let h0' = get () in
  let n = tail_cell #a ptr in
  from_list_cell n;
  n


let ind_llist_sl' (#a:Type0) (r:ref (t a)) (p:t a) : slprop u#1 =
  R.pts_to r full_perm p `Mem.star` llist_sl p
let ind_llist_sl (#a:Type0) (r:ref (t a)) = h_exists (ind_llist_sl' r)

let ind_llist_sel_full' (#a:Type0) (r:ref (t a)) : selector' (t a * list a) (ind_llist_sl r) =
  fun h ->
    let p = id_elim_exists (ind_llist_sl' r) h in
    (reveal p, llist_sel p h)

let ind_llist_sel_depends_only_on (#a:Type0) (ptr:ref (t a))
  (m0:Mem.hmem (ind_llist_sl ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (ind_llist_sel_full' ptr m0 == ind_llist_sel_full' ptr (Mem.join m0 m1))
  = let m' = Mem.join m0 m1 in
    let p1 = reveal (id_elim_exists (ind_llist_sl' ptr) m0) in
    let p2 = reveal (id_elim_exists (ind_llist_sl' ptr) m') in

    R.pts_to_witinv ptr full_perm;
    Mem.elim_wi (ind_llist_sl' ptr) p1 p2 m'

let ind_llist_sel_depends_only_on_core (#a:Type0) (ptr:ref (t a))
  (m0:Mem.hmem (ind_llist_sl ptr))
  : Lemma (ind_llist_sel_full' ptr m0 == ind_llist_sel_full' ptr (core_mem m0))
  = let p1 = reveal (id_elim_exists (ind_llist_sl' ptr) m0) in
    let p2 = reveal (id_elim_exists (ind_llist_sl' ptr) (core_mem m0)) in

    R.pts_to_witinv ptr full_perm;
    Mem.elim_wi (ind_llist_sl' ptr) p1 p2 (core_mem m0)

let ind_llist_sel_full (#a:Type0) (r:ref (t a)) : selector (t a * list a) (ind_llist_sl r) =
  Classical.forall_intro_2 (ind_llist_sel_depends_only_on r);
  Classical.forall_intro (ind_llist_sel_depends_only_on_core r);
  ind_llist_sel_full' r

let ind_llist_sel r = fun h -> snd (ind_llist_sel_full r h)

[@@__steel_reduce__]
let ind_llist_full' #a r : vprop' =
  {hp = ind_llist_sl r;
   t = t a * list a;
   sel = ind_llist_sel_full r}
unfold
let ind_llist_full (#a:Type0) (r:ref (t a)) = VUnit (ind_llist_full' r)

[@@ __steel_reduce__]
let v_full (#a:Type0) (#p:vprop) (r:ref (t a))
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (ind_llist_full r) /\ True)})
  = h (ind_llist_full r)

let intro_ptr_frame_lemma (#a:Type0) (r:ref a) (x:a) (frame:slprop) (m:mem)
  : Lemma (requires interp (R.pts_to r full_perm x `Mem.star` frame) m)
          (ensures interp (ptr r `Mem.star` frame) m /\ sel_of (vptr r) m == x)
  = let aux (m:mem) (ml mr:mem) : Lemma
      (requires disjoint ml mr /\ m == join ml mr /\
        interp (R.pts_to r full_perm x) ml /\ interp frame mr)
      (ensures interp (ptr r `Mem.star` frame) m /\
        sel_of (vptr r) m == x)
      = intro_h_exists (hide x) (R.pts_to r full_perm) ml;
        intro_star (ptr r) frame ml mr;
        ptr_sel_interp r ml;
        R.pts_to_witinv r full_perm
    in
    elim_star (R.pts_to r full_perm x) frame m;
    Classical.forall_intro_2 (Classical.move_requires_2 (aux m))

let intro_pts_to_frame_lemma (#a:Type0) (r:ref a) (x:a) (frame:slprop) (m:mem)
  : Lemma (requires interp (ptr r `Mem.star` frame) m /\ sel_of (vptr r) m == x)
          (ensures interp (R.pts_to r full_perm x `Mem.star` frame) m)
  = let aux (m:mem) (ml mr:mem) : Lemma
      (requires disjoint ml mr /\ m == join ml mr /\
        interp (ptr r) ml /\ interp frame mr /\ sel_of (vptr r) ml == x)
      (ensures interp (R.pts_to r full_perm x `Mem.star` frame) m)
      = ptr_sel_interp r ml;
        intro_star (R.pts_to r full_perm x) frame ml mr
    in
    elim_star (ptr r) frame m;
    Classical.forall_intro_2 (Classical.move_requires_2 (aux m))


let unpack_ind_lemma (#a:Type0) (r:ref (t a)) (p:t a) (l:list a) (m:mem) : Lemma
  (requires interp (ind_llist_sl r) m /\ ind_llist_sel_full r m == (p, l))
  (ensures
    interp (ptr r `Mem.star` llist_sl p) m /\
    sel_of (vptr r) m == p /\
    sel_of (llist p) m == l)
  = intro_ptr_frame_lemma r p (llist_sl p) m

val unpack_ind_full (#a:Type0) (r:ref (t a))
  : SteelSel (t a)
             (ind_llist_full r)
             (fun p -> vptr r `star` llist p)
             (requires fun _ -> True)
             (ensures fun h0 p h1 ->
               sel r h1 == p /\
               p == fst (v_full r h0) /\
               v_llist p h1 == snd (v_full r h0))

let unpack_ind_full r =
    let h = get () in
    let s = hide (v_full r h) in
    let gp = hide (fst (reveal s)) in
    let gl = hide (snd (reveal s)) in
    change_slprop
      (ind_llist_full r)
      (vptr r `star` llist (reveal gp))
      s
      (reveal gp, reveal gl)
      (fun m -> unpack_ind_lemma r gp gl m);
    reveal_star (vptr r) (llist (reveal gp));
    let p = read r in
    change_slprop_rel (llist (reveal gp)) (llist p) (fun x y -> x == y) (fun _ -> ());
    return p

let unpack_ind r =
  change_slprop_rel (ind_llist r) (ind_llist_full r) (fun x y -> x == snd y) (fun _ -> ());
  let p = unpack_ind_full r in
  p

let pack_ind_lemma (#a:Type0) (r:ref (t a)) (p:t a) (l:list a) (m:mem)
  : Lemma
    (requires
      interp (ptr r `Mem.star` llist_sl p) m /\
      sel_of (vptr r) m == p /\
      sel_of (llist p) m == l)
    (ensures interp (ind_llist_sl r) m /\ sel_of (ind_llist r) m == l)
  = intro_pts_to_frame_lemma r p (llist_sl p) m;
    intro_h_exists p (ind_llist_sl' r) m;
    let (p', l') = ind_llist_sel_full r m in
    unpack_ind_lemma r p' l' m;
    R.pts_to_witinv r full_perm

let pack_ind r p =
  let h = get () in
  reveal_star (vptr r) (llist p);
  let gl = hide (v_llist p h) in
  change_slprop (vptr r `star` llist p) (ind_llist r) (p, reveal gl) gl (fun m -> pack_ind_lemma r p gl m)

#pop-options
