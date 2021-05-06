module Selectors.PtrLList

open FStar.Ghost
open Steel.FractionalPermission
module Mem = Steel.Memory
module R = Steel.Reference
open Steel.SelEffect.Atomic
open Steel.SelEffect
open Steel.SelReference

#push-options "--__no_positivity"
noeq
type cell (a:Type0) = {
  next : ref (cell a);
  data : ref a;
}
#pop-options

let next #a (c:cell a) : t a = c.next
let data #a (c:cell a) : ref a = c.data
let mk_cell #a (n: t a) (d:ref a) = {
  next = n;
  data = d
}

let null_llist #a = R.null
let is_null #a ptr = R.is_null ptr

let rec llist_ptr_sl' (#a:Type0) (ptr:t a) (l:list (cell a * a))
  : Tot slprop (decreases l)
  = match l with
    | [] -> Mem.pure (ptr == null_llist)
    | (hd, v) :: tl ->
      R.pts_to ptr full_perm hd `Mem.star`
      llist_ptr_sl' (next hd) tl `Mem.star`
      R.pts_to (data hd) full_perm v `Mem.star`
      Mem.pure (ptr =!= null_llist)

let llist_ptr_sl ptr = Mem.h_exists (llist_ptr_sl' ptr)

val llist_ptr_sel' (#a:Type0) (ptr:t a) : selector' (list (cell a * a)) (llist_ptr_sl ptr)

let llist_ptr_sel' #a ptr = fun h -> id_elim_exists (llist_ptr_sl' ptr) h

let llist_ptr_sl'_witinv (#a:Type) (ptr:t a)
  : Lemma (is_witness_invariant (llist_ptr_sl' ptr))
  = let rec aux (ptr:t a) (x y:list (cell a * a)) (m:mem) : Lemma
        (requires interp (llist_ptr_sl' ptr x) m /\ interp (llist_ptr_sl' ptr y) m)
        (ensures x == y)
        (decreases x)
     = match x with
       | [] -> begin match y with
         | [] -> ()
         | (hd, v)::tl ->
           Mem.pure_interp (ptr == null_llist) m;
           Mem.pure_star_interp
             (R.pts_to ptr full_perm hd `Mem.star`
              llist_ptr_sl' (next hd) tl `Mem.star`
              R.pts_to (data hd) full_perm v)
             (ptr =!= null_llist) m;
           Mem.pure_interp (ptr =!= null_llist) m
         end
       | (hd1, v1)::tl1 -> begin match y with
         | [] ->
           Mem.pure_interp (ptr == null_llist) m;
           Mem.pure_star_interp
             (R.pts_to ptr full_perm hd1 `Mem.star`
              llist_ptr_sl' (next hd1) tl1 `Mem.star`
              R.pts_to (data hd1) full_perm v1)
             (ptr =!= null_llist) m;
           Mem.pure_interp (ptr =!= null_llist) m
         | (hd2, v2)::tl2 ->
           R.pts_to_witinv ptr full_perm;
           R.pts_to_witinv (data hd1) full_perm;
           aux (next hd1) tl1 tl2 m

       end


    in Classical.forall_intro_3 (Classical.move_requires_3 (aux ptr))


let llist_sel_depends_only_on (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (llist_ptr_sl ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (llist_ptr_sel' ptr m0 == llist_ptr_sel' ptr (Mem.join m0 m1))
  = let l1 = reveal (id_elim_exists (llist_ptr_sl' ptr) m0) in
    let l2 = reveal (id_elim_exists (llist_ptr_sl' ptr) (Mem.join m0 m1)) in

    llist_ptr_sl'_witinv ptr;
    Mem.elim_wi (llist_ptr_sl' ptr) l1 l2 (Mem.join m0 m1)

let llist_sel_depends_only_on_core (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (llist_ptr_sl ptr))
  : Lemma (llist_ptr_sel' ptr m0 == llist_ptr_sel' ptr (core_mem m0))
  = let l1 = reveal (id_elim_exists (llist_ptr_sl' ptr) m0) in
    let l2 = reveal (id_elim_exists (llist_ptr_sl' ptr) (core_mem m0)) in

    llist_ptr_sl'_witinv ptr;
    Mem.elim_wi (llist_ptr_sl' ptr) l1 l2 (core_mem m0)

val llist_ptr_sel_cell (#a:Type0) (ptr:t a) : selector (list (cell a * a)) (llist_ptr_sl ptr)
let llist_ptr_sel_cell #a ptr =
  Classical.forall_intro_2 (llist_sel_depends_only_on ptr);
  Classical.forall_intro (llist_sel_depends_only_on_core ptr);
  llist_ptr_sel' ptr

let rec datas (#a:Type) (l:list (cell a * a)) : list a =
  match l with
  | [] -> []
  | (_, v)::tl -> v :: datas tl

let llist_ptr_sel ptr = fun h -> datas (llist_ptr_sel_cell ptr h)

[@@__steel_reduce__]
let llist_cell' #a r : vprop' =
  {hp = llist_ptr_sl r;
   t = list (cell a * a);
   sel = llist_ptr_sel_cell r}
unfold
let llist_cell (#a:Type0) (r:t a) = VUnit (llist_cell' r)

[@@ __steel_reduce__]
let v_cell (#a:Type0) (#p:vprop) (r:t a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (llist_cell r) /\ True)}) : GTot (list (cell a * a))
  = h (llist_cell r)

(* Indirection pointer on a pointer. Should become a generic module at some point *)

let ind_ptr_sl' (#a:Type0) (r:ref (ref a)) (p: ref a) : slprop u#1 =
  R.pts_to r full_perm p `Mem.star` ptr p
let ind_ptr_sl (#a:Type0) (r:ref (ref a)) = h_exists (ind_ptr_sl' r)

let ind_ptr_sel' (#a:Type0) (r:ref (ref a)) : selector' (ref a * a) (ind_ptr_sl r) =
  fun h ->
    let p = id_elim_exists (ind_ptr_sl' r) h in
    reveal p, ptr_sel p h

let ind_ptr_sel_depends_only_on (#a:Type0) (ptr:ref (ref a))
  (m0:Mem.hmem (ind_ptr_sl ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (ind_ptr_sel' ptr m0 == ind_ptr_sel' ptr (Mem.join m0 m1))
  = let p1 = reveal (id_elim_exists (ind_ptr_sl' ptr) m0) in
    let p2 = reveal (id_elim_exists (ind_ptr_sl' ptr) (Mem.join m0 m1)) in
    R.pts_to_witinv ptr full_perm;
    elim_wi (ind_ptr_sl' ptr) p1 p2 (Mem.join m0 m1)

let ind_ptr_sel_depends_only_on_core (#a:Type0) (ptr:ref (ref a))
  (m0:Mem.hmem (ind_ptr_sl ptr))
  : Lemma (ind_ptr_sel' ptr m0 == ind_ptr_sel' ptr (core_mem m0))
  = let p1 = reveal (id_elim_exists (ind_ptr_sl' ptr) m0) in
    let p2 = reveal (id_elim_exists (ind_ptr_sl' ptr) (core_mem m0)) in
    R.pts_to_witinv ptr full_perm;
    elim_wi (ind_ptr_sl' ptr) p1 p2 (core_mem m0)

let ind_ptr_sel_full (#a:Type0) (r:ref (ref a)) : selector (ref a * a) (ind_ptr_sl r) =
  Classical.forall_intro_2 (ind_ptr_sel_depends_only_on r);
  Classical.forall_intro (ind_ptr_sel_depends_only_on_core r);
  ind_ptr_sel' r

let ind_ptr_sel (#a:Type0) (r:ref (ref a)) : selector a (ind_ptr_sl r) =
  fun h -> snd (ind_ptr_sel_full r h)

[@@__steel_reduce__]
let ind_ptr_full' (#a:Type0) (r:ref (ref a)) : vprop' =
  { hp = ind_ptr_sl r;
    t = ref a * a;
    sel = ind_ptr_sel_full r}
unfold
let ind_ptr_full (#a:Type0) (r:ref (ref a)) = VUnit (ind_ptr_full' r)

[@@__steel_reduce__]
let ind_ptr' (#a:Type0) (r:ref (ref a)) : vprop' =
  { hp = ind_ptr_sl r;
    t = a;
    sel = ind_ptr_sel r}
unfold
let ind_ptr (#a:Type0) (r:ref (ref a)) = VUnit (ind_ptr' r)

[@@ __steel_reduce__]
let v_full (#a:Type0) (#p:vprop) (r:ref (ref a))
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (ind_ptr_full r) /\ True)})
  = h (ind_ptr_full r)

[@@ __steel_reduce__]
let ind_sel (#a:Type0) (#p:vprop) (r:ref (ref a))
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (ind_ptr r) /\ True)})
  = h (ind_ptr r)

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

let unpack_ind_lemma (#a:Type0) (r:ref (ref a)) (p:ref a) (v:a) (m:mem) : Lemma
  (requires interp (ind_ptr_sl r) m /\ ind_ptr_sel_full r m == (p, v))
  (ensures
    interp (ptr r `Mem.star` ptr p) m /\
    sel_of (vptr r) m == p /\
    sel_of (vptr p) m == v)
  = intro_ptr_frame_lemma r p (ptr p) m

val unpack_ind_full (#a:Type0) (r:ref (ref a))
  : SteelSel (ref a)
             (ind_ptr_full r)
             (fun p -> vptr r `star` vptr p)
             (requires fun _ -> True)
             (ensures fun h0 p h1 ->
               sel r h1 == p /\
               p == fst (v_full r h0) /\
               sel p h1 == snd (v_full r h0))

let unpack_ind_full r =
    let h = get () in
    let s = hide (v_full r h) in
    let gp = hide (fst (reveal s)) in
    let gl = hide (snd (reveal s)) in
    change_slprop
      (ind_ptr_full r)
      (vptr r `star` vptr (reveal gp))
      s
      (reveal gp, reveal gl)
      (fun m -> unpack_ind_lemma r gp gl m);
    reveal_star (vptr r) (vptr (reveal gp));
    let p = read r in
    change_slprop_rel (vptr (reveal gp)) (vptr p) (fun x y -> x == y) (fun _ -> ());
    return p

val unpack_ind (#a:Type0) (r:ref (ref a))
  : SteelSel (ref a)
             (ind_ptr r)
             (fun p -> vptr r `star` vptr p)
             (requires fun _ -> True)
             (ensures fun h0 p h1 ->
               sel r h1 == p /\
               sel p h1 == ind_sel r h0)

let unpack_ind r =
  change_slprop_rel (ind_ptr r) (ind_ptr_full r) (fun x y -> x == snd y) (fun _ -> ());
  let p = unpack_ind_full r in
  p

val pack_ind (#a:Type0) (r:ref (ref a)) (p:ref a)
  : SteelSel unit
             (vptr r `star` vptr p)
             (fun _ -> ind_ptr r)
             (requires fun h -> sel r h == p)
             (ensures fun h0 _ h1 -> sel p h0 == ind_sel r h1)

let pack_ind_lemma (#a:Type0) (r:ref (ref a)) (p:ref a) (v:a) (m:mem)
  : Lemma
    (requires
      interp (ptr r `Mem.star` ptr p) m /\
      sel_of (vptr r) m == p /\
      sel_of (vptr p) m == v)
    (ensures interp (ind_ptr_sl r) m /\ sel_of (ind_ptr r) m == v)
  = intro_pts_to_frame_lemma r p (ptr p) m;
    intro_h_exists p (ind_ptr_sl' r) m;
    let (p', l') = ind_ptr_sel_full r m in
    unpack_ind_lemma r p' l' m;
    R.pts_to_witinv r full_perm

let pack_ind r p =
  let h = get #(vptr r `star` vptr p) () in
  reveal_star (vptr r) (vptr p);
  let gl = hide (sel p h) in
  change_slprop (vptr r `star` vptr p) (ind_ptr r) (p, reveal gl) gl (fun m -> pack_ind_lemma r p gl m)

let llist_sel_interp (#a:Type0) (ptr:t a) (l:list (cell a * a)) (m:mem) : Lemma
  (requires interp (llist_ptr_sl' ptr l) m)
  (ensures interp (llist_ptr_sl ptr) m /\ llist_ptr_sel_cell ptr m == l)
  = intro_h_exists l (llist_ptr_sl' ptr) m;
    llist_ptr_sl'_witinv ptr

let reveal_non_empty_lemma (#a:Type) (ptr:t a) (l:list (cell a * a)) (m:mem) : Lemma
    (requires interp (llist_ptr_sl ptr) m /\ llist_ptr_sel_cell ptr m == l /\ ptr =!= null_llist)
    (ensures Cons? l)
= let l' = id_elim_exists (llist_ptr_sl' ptr) m in
  llist_sel_interp ptr l' m;
  pure_interp (ptr == null_llist) m

val reveal_non_empty_cell (#a:Type0) (ptr:t a)
  : SteelSel unit (llist_cell ptr) (fun _ -> llist_cell ptr)
             (requires fun _ -> ptr =!= null_llist)
             (ensures fun h0 _ h1 -> v_cell ptr h0 == v_cell ptr h1 /\ Cons? (v_cell ptr h0))

let is_cons (#a:Type) (l:list a) : prop = match l with
  | [] -> False
  | _ -> True

let reveal_non_empty_cell #a ptr =
  let h = get #(llist_cell ptr)  () in
  let l = hide (v_cell ptr h) in
  extract_info (llist_cell ptr) l (is_cons l) (reveal_non_empty_lemma ptr l)


let intro_nil_lemma (a:Type0) (m:mem) : Lemma
    (requires interp (hp_of emp) m)
    (ensures interp (llist_ptr_sl (null_llist #a)) m /\ llist_ptr_sel (null_llist #a) m == [])
    = let ptr:t a = null_llist in
      pure_interp (ptr == null_llist) m;
      let open FStar.Tactics in
      assert (llist_ptr_sl' ptr [] == Mem.pure (ptr == null_llist)) by (norm [delta; zeta; iota]);
      llist_sel_interp ptr [] m

let intro_llist_nil a =
    change_slprop_2 emp (llist_ptr (null_llist #a)) ([] <: list a) (intro_nil_lemma a)

let elim_nil_lemma (#a:Type0) (ptr:t a) (m:mem) : Lemma
    (requires interp (llist_ptr_sl ptr) m /\ ptr == null_llist)
    (ensures interp (llist_ptr_sl ptr) m /\ llist_ptr_sel ptr m == [])
    = let l' = id_elim_exists (llist_ptr_sl' ptr) m in
      pure_interp (ptr == null_llist) m;
      llist_sel_interp ptr [] m

let elim_llist_nil #a ptr =
  change_slprop_rel (llist_ptr ptr) (llist_ptr ptr)
    (fun x y -> x == y /\ y == [])
    (fun m -> elim_nil_lemma ptr m)

let lemma_cons_not_null (#a:Type) (ptr:t a) (l:list a) (m:mem) : Lemma
    (requires interp (llist_ptr_sl ptr) m /\ llist_ptr_sel ptr m == l /\ Cons? l)
    (ensures ptr =!= null_llist)
    = let l' = id_elim_exists (llist_ptr_sl' ptr) m in
      assert (interp (llist_ptr_sl' ptr l') m);
      llist_sel_interp ptr l' m;
      match reveal l' with
      | (hd, v)::tl ->
          let p = R.pts_to ptr full_perm (hide hd) `Mem.star`
            llist_ptr_sl' (next hd) tl `Mem.star`
            R.pts_to (data hd) full_perm (hide v) in
          pure_star_interp p (ptr =!= null_llist) m

let cons_is_not_null #a ptr =
  let h = get #(llist_ptr ptr)  () in
  let l = hide (v_ptrlist ptr h) in
  extract_info (llist_ptr ptr) l (ptr =!= null_llist) (lemma_cons_not_null ptr l)


let intro_cons_lemma_aux (#a:Type0) (ptr1:t a)
  (x: cell a) (v:a) (l:list (cell a * a)) (m:mem) : Lemma
  (requires
    interp (R.pts_to ptr1 full_perm x `Mem.star`
      llist_ptr_sl' (next x) l `Mem.star`
      R.pts_to (data x) full_perm v)
    m)
  (ensures interp (llist_ptr_sl' ptr1 ((x, v)::l)) m)
  = affine_star
      (R.pts_to ptr1 full_perm x `Mem.star` llist_ptr_sl' (next x) l)
      (R.pts_to (data x) full_perm v)
      m;
    affine_star (R.pts_to ptr1 full_perm x) (llist_ptr_sl' (next x) l) m;
    R.pts_to_not_null ptr1 full_perm x m;
    emp_unit
     (R.pts_to ptr1 full_perm x `Mem.star`
      llist_ptr_sl' (next x) l `Mem.star`
      R.pts_to (data x) full_perm v);
    pure_star_interp
      (R.pts_to ptr1 full_perm x `Mem.star`
        llist_ptr_sl' (next x) l `Mem.star` R.pts_to (data x) full_perm v)
      (ptr1 =!= null_llist)
      m

let intro_cons_lemma (#a:Type0) (ptr1:t a)
  (x: cell a) (v:a) (l:list a) (m:mem) : Lemma
  (requires interp (ptr ptr1 `Mem.star` llist_ptr_sl (next x) `Mem.star` ptr (data x)) m /\
    sel_of (vptr ptr1) m == x /\
    sel_of (llist_ptr (next x)) m == l /\
    sel_of (vptr (data x)) m == v)
  (ensures interp (llist_ptr_sl ptr1) m /\ llist_ptr_sel ptr1 m == v :: l)
  = let l' = id_elim_exists (llist_ptr_sl' (next x)) m in
    assert (interp (llist_ptr_sl' (next x) l') m);
    let aux (m:mem) (ml1 ml2 mr:mem) : Lemma
      (requires disjoint ml1 ml2 /\ disjoint (join ml1 ml2) mr /\ m == join (join ml1 ml2) mr /\
        interp (ptr ptr1) ml1 /\ interp (llist_ptr_sl (next x)) ml2 /\ interp (ptr (data x)) mr /\
        interp (ptr (data x)) m /\ ptr_sel (data x) m == v /\
        interp (llist_ptr_sl' (next x) l') m /\
        ptr_sel ptr1 ml1 == x
      )
      (ensures interp
        (R.pts_to ptr1 full_perm x `Mem.star`
         llist_ptr_sl' (next x) l' `Mem.star`
         R.pts_to (data x) full_perm v) m)
      = ptr_sel_interp ptr1 ml1;
        let l2 = id_elim_exists (llist_ptr_sl' (next x)) ml2 in
        join_commutative ml1 ml2;
        assert (interp (llist_ptr_sl' (next x) l2) m);
        llist_ptr_sl'_witinv (next x);
        assert (l2 == l');
        assert (interp (llist_ptr_sl' (next x) l') ml2);
        ptr_sel_interp (data x) mr;
        join_commutative (join ml1 ml2) mr;
        assert (ptr_sel (data x) mr == v);
        assert (interp (R.pts_to (data x) full_perm v) mr);
        intro_star (R.pts_to ptr1 full_perm x) (llist_ptr_sl' (next x) l') ml1 ml2;
        intro_star
          (R.pts_to ptr1 full_perm x `Mem.star` llist_ptr_sl' (next x) l')
          (R.pts_to (data x) full_perm v)
          (join ml1 ml2) mr
    in
    elim_star
      (ptr ptr1 `Mem.star` llist_ptr_sl (next x))
      (ptr (data x)) m;
    Classical.forall_intro (Classical.move_requires
      (elim_star (ptr ptr1) (llist_ptr_sl (next x))));
    Classical.forall_intro_3 (Classical.move_requires_3 (aux m));
    intro_cons_lemma_aux ptr1 x v l' m;
    assert (interp (llist_ptr_sl' ptr1 ((x,v)::l')) m);
    intro_h_exists ((x,v)::l') (llist_ptr_sl' ptr1) m;
    llist_sel_interp ptr1 ((x,v)::l') m

#push-options "--fuel 1 --ifuel 1"

let intro_llist_cons ptr1 ptr2 r =
  let h = get () in
  let x = hide (sel ptr1 h) in
  let v = hide (sel r h) in
  let l = hide (v_ptrlist ptr2 h) in
  reveal_star_3 (vptr ptr1) (llist_ptr ptr2) (vptr r);

  change_slprop (vptr ptr1 `star` llist_ptr ptr2 `star` vptr r) (llist_ptr ptr1)
    ((reveal x, reveal l), reveal v)
  (reveal v :: l) (fun m -> intro_cons_lemma ptr1 x v l m)


val elim_cons_cell (#a:Type0) (ptr:t a)
  : SteelSel (cell a) (llist_cell ptr)
                   (fun c -> vptr ptr `star` vptr (data c) `star` llist_cell (next c))
                   (requires fun _ -> ptr =!= null_llist)
                   (ensures fun h0 c h1 ->
                     Cons? (v_cell ptr h0) /\
                     c == sel ptr h1 /\
                     sel ptr h1 == fst (L.hd (v_cell ptr h0)) /\
                     sel (data c) h1 == snd (L.hd (v_cell ptr h0)) /\
                     v_cell (next c) h1 == L.tl (v_cell ptr h0))


let elim_cons_cell_lemma (#a:Type0) (r:t a) (l:list (cell a * a)) (m:mem) : Lemma
  (requires Cons? l /\ interp (llist_ptr_sl r) m /\ llist_ptr_sel_cell r m == l)
  (ensures (let x = fst (L.hd l) in
    interp (ptr r `Mem.star` llist_ptr_sl (next x) `Mem.star` ptr (data x)) m /\
    sel_of (vptr r) m == x /\
    sel_of (vptr (data x)) m == snd (L.hd l) /\
    sel_of (llist_cell (next x)) m == L.tl l))
  = llist_sel_interp r l m;
    assert (interp (llist_ptr_sl' r l) m);
    let x = fst (L.hd l) in
    let v = snd (L.hd l) in
    let tl = L.tl l in
    let sl = R.pts_to r full_perm x `Mem.star` llist_ptr_sl' (next x) tl `Mem.star` R.pts_to (data x) full_perm v in
    pure_star_interp sl (r =!= null_llist) m;
    emp_unit sl;
    assert (interp sl m);
    let aux (m:mem) (ml1 ml2 mr:mem) : Lemma
      (requires disjoint ml1 ml2 /\ disjoint (join ml1 ml2) mr /\ m == join (join ml1 ml2) mr /\
        interp (R.pts_to r full_perm x) ml1 /\
        interp (llist_ptr_sl' (next x) tl) ml2 /\
        interp (R.pts_to (data x) full_perm v) mr)
      (ensures interp (ptr r `Mem.star` llist_ptr_sl (next x) `Mem.star` ptr (data x)) m /\
        sel_of (vptr r) m == x /\
        sel_of (llist_cell (next x)) m == tl /\
        sel_of (vptr (data x)) m == v)
      = intro_h_exists (hide x) (R.pts_to r full_perm) ml1;
        llist_sel_interp (next x) tl ml2;
        intro_star (ptr r) (llist_ptr_sl (next x)) ml1 ml2;
        ptr_sel_interp r ml1;
        R.pts_to_witinv r full_perm;
        join_commutative ml1 ml2;
        let ml = join ml1 ml2 in
        assert (interp (ptr r `Mem.star` llist_ptr_sl (next x)) ml);
        intro_h_exists (hide v) (R.pts_to (data x) full_perm) mr;
        intro_star (ptr r `Mem.star` llist_ptr_sl (next x)) (ptr (data x)) ml mr;
        ptr_sel_interp (data x) mr;
        R.pts_to_witinv (data x) full_perm;
        join_commutative ml mr
    in
    elim_star
      (R.pts_to r full_perm x `Mem.star` llist_ptr_sl' (next x) tl)
      (R.pts_to (data x) full_perm v) m;
    Classical.forall_intro (Classical.move_requires
      (elim_star (R.pts_to r full_perm x) (llist_ptr_sl' (next x) tl)));
    Classical.forall_intro_3 (Classical.move_requires_3 (aux m))

let elim_cons_cell #a ptr =
  let h = get () in
  let l = hide (v_cell ptr h) in
  reveal_non_empty_cell ptr;
  let gc = hide (fst (L.hd l)) in
  change_slprop
    (llist_cell ptr)
    (vptr ptr `star` llist_cell (next gc) `star`  vptr (data gc))
    l ((reveal gc, L.tl l), snd (L.hd l)) (fun m -> elim_cons_cell_lemma ptr l m);
  reveal_star (vptr ptr `star` llist_cell (next gc)) (vptr (data gc));
  reveal_star (vptr ptr) (llist_cell (next gc));
  let c = read ptr in
  change_slprop (llist_cell (next gc)) (llist_cell (next c)) (L.tl l) (L.tl l) (fun _ -> ());
  change_slprop (vptr (data gc)) (vptr (data c)) (snd (L.hd l)) (snd (L.hd l)) (fun _ -> ());
  return c

let elim_llist_cons ptr =
  change_slprop_rel (llist_ptr ptr) (llist_cell ptr) (fun x y -> x == datas y) (fun _ -> ());
  let h = get () in
  let c = elim_cons_cell ptr in
  change_slprop_rel (llist_cell (next c)) (llist_ptr (next c)) (fun x y -> datas x == y) (fun _ -> ());
  return c
