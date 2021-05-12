module Selectors.LList

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module L = FStar.List.Tot


val cell (a:Type0) : Type0
let t (a:Type0) = ref (cell a)

val next (#a:Type0) (c:cell a) : t a
val data (#a:Type0) (c:cell a) : a
val mk_cell (#a:Type0) (n: t a) (d:a)
  : Pure (cell a)
    (requires True)
    (ensures fun c ->
      next c == n /\
      data c == d)


val null_llist (#a:Type) : t a
val is_null (#a:Type) (ptr:t a) : (b:bool{b <==> ptr == null_llist})


val llist_sl (#a:Type0) (r:t a) : slprop u#1
val llist_sel (#a:Type0) (r:t a) : selector (list a) (llist_sl r)

[@@__steel_reduce__]
let llist' #a r : vprop' =
  {hp = llist_sl r;
   t = list a;
   sel = llist_sel r}
unfold
let llist (#a:Type0) (r:t a) = VUnit (llist' r)

[@@ __steel_reduce__]
let v_llist (#a:Type0) (#p:vprop) (r:t a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (llist r) /\ True)}) : GTot (list a)
  = h (llist r)

val intro_llist_nil (a:Type0)
  : Steel unit emp (fun _ -> llist (null_llist #a))
          (requires fun _ -> True)
          (ensures fun _ _ h1 -> v_llist #a null_llist h1 == [])

val elim_llist_nil (#a:Type0) (ptr:t a)
  : Steel unit (llist ptr) (fun _ -> llist ptr)
          (requires fun _ -> ptr == null_llist)
          (ensures fun h0 _ h1 ->
            v_llist ptr h0 == v_llist ptr h1 /\
            v_llist ptr h1 == [])

val cons_is_not_null (#a:Type0) (ptr:t a)
  : Steel unit (llist ptr) (fun _ -> llist ptr)
             (requires fun h -> Cons? (v_llist ptr h))
             (ensures fun h0 _ h1 ->
               v_llist ptr h0 == v_llist ptr h1 /\
               ptr =!= null_llist)

val intro_llist_cons (#a:Type0) (ptr1 ptr2:t a)
  : Steel unit (vptr ptr1 `star` llist ptr2)
                  (fun _ -> llist ptr1)
                  (requires fun h -> next (sel ptr1 h) == ptr2)
                  (ensures fun h0 _ h1 -> v_llist ptr1 h1 == (data (sel ptr1 h0)) :: v_llist ptr2 h0)

val tail (#a:Type0) (ptr:t a)
  : Steel (t a) (llist ptr)
                   (fun n -> vptr ptr `star` llist n)
                   (requires fun _ -> ptr =!= null_llist)
                   (ensures fun h0 n h1 ->
                     Cons? (v_llist ptr h0) /\
                     sel ptr h1 == mk_cell n (L.hd (v_llist ptr h0)) /\
                     v_llist n h1 == L.tl (v_llist ptr h0))


val ind_llist_sl (#a:Type0) (r:ref (t a)) : slprop u#1
val ind_llist_sel (#a:Type0) (r:ref (t a)) : selector (list a) (ind_llist_sl r)

[@@__steel_reduce__]
let ind_llist' (#a:Type0) (r:ref (t a)) : vprop' =
  { hp = ind_llist_sl r;
    t = list a;
    sel = ind_llist_sel r}
unfold
let ind_llist (#a:Type0) (r:ref (t a)) = VUnit (ind_llist' r)

[@@ __steel_reduce__]
let v_ind_llist (#a:Type0) (#p:vprop) (r:ref (t a))
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (ind_llist r) /\ True)}) : GTot (list a)
  = h (ind_llist r)

val unpack_ind (#a:Type0) (r:ref (t a))
  : Steel (t a)
             (ind_llist r)
             (fun p -> vptr r `star` llist p)
             (requires fun _ -> True)
             (ensures fun h0 p h1 ->
               sel r h1 == p /\
               v_llist p h1 == v_ind_llist r h0)

val pack_ind (#a:Type0) (r:ref (t a)) (p:t a)
  : Steel unit
             (vptr r `star` llist p)
             (fun _ -> ind_llist r)
             (requires fun h -> sel r h == p)
             (ensures fun h0 _ h1 -> v_llist p h0 == v_ind_llist r h1)
