module Selectors.PtrLList

open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect

module L = FStar.List.Tot

val cell (a:Type0) : Type0
let t (a:Type0) = ref (cell a)

val next (#a:Type0) (c:cell a) : t a
val data (#a:Type0) (c:cell a) : ref a
val mk_cell (#a:Type0) (n: t a) (d:ref a)
  : Pure (cell a)
    (requires True)
    (ensures fun c ->
      next c == n /\
      data c == d)

val null_llist (#a:Type) : t a
val is_null (#a:Type) (ptr:t a) : (b:bool{b <==> ptr == null_llist})

val llist_ptr_sl (#a:Type0) (r:t a) : slprop u#1
val llist_ptr_sel (#a:Type0) (r:t a) : selector (list a) (llist_ptr_sl r)

[@@__steel_reduce__]
let llist_ptr' (#a:Type0) (r:t a) : vprop' =
  { hp = llist_ptr_sl r;
    t = list a;
    sel = llist_ptr_sel r}
unfold
let llist_ptr (#a:Type0) (r:t a) = VUnit (llist_ptr' r)

[@@ __steel_reduce__]
let v_ptrlist (#a:Type0) (#p:vprop) (r:t a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (llist_ptr r) /\ True)}) : GTot (list a)
  = h (llist_ptr r)

val intro_llist_nil (a:Type0)
  : SteelSel unit vemp (fun _ -> llist_ptr (null_llist #a))
          (requires fun _ -> True)
          (ensures fun _ _ h1 -> v_ptrlist #a null_llist h1 == [])

val elim_llist_nil (#a:Type0) (ptr:t a)
  : SteelSel unit (llist_ptr ptr) (fun _ -> llist_ptr ptr)
          (requires fun _ -> ptr == null_llist)
          (ensures fun h0 _ h1 ->
            v_ptrlist ptr h0 == v_ptrlist ptr h1 /\
            v_ptrlist ptr h1 == [])

val cons_is_not_null (#a:Type0) (ptr:t a)
  : SteelSel unit (llist_ptr ptr) (fun _ -> llist_ptr ptr)
             (requires fun h -> Cons? (v_ptrlist ptr h))
             (ensures fun h0 _ h1 ->
               v_ptrlist ptr h0 == v_ptrlist ptr h1 /\
               ptr =!= null_llist)

val intro_llist_cons (#a:Type0) (ptr1 ptr2:t a) (r:ref a)
  : SteelSel unit (vptr ptr1 `star` vptr r `star` llist_ptr ptr2)
                  (fun _ -> llist_ptr ptr1)
                  (requires fun h -> data (sel ptr1 h) == r /\ next (sel ptr1 h) == ptr2)
                  (ensures fun h0 _ h1 -> v_ptrlist ptr1 h1 == (sel r h0) :: v_ptrlist ptr2 h0)

val elim_llist_cons (#a:Type0) (ptr:t a)
  : SteelSel (cell a)
             (llist_ptr ptr)
             (fun c -> vptr ptr `star` vptr (data c) `star` llist_ptr (next c))
             (requires fun h -> ptr =!= null_llist)
             (ensures fun h0 c h1 ->
               Cons? (v_ptrlist ptr h0) /\
               sel ptr h1 == c /\
               sel (data c) h1 == L.hd (v_ptrlist ptr h0) /\
               v_ptrlist (next c) h1 == L.tl (v_ptrlist ptr h0)
             )
