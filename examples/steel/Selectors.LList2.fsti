module Selectors.LList2

open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect

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
  : SteelSel unit vemp (fun _ -> llist (null_llist #a))
          (requires fun _ -> True)
          (ensures fun _ _ h1 -> v_llist #a null_llist h1 == [])

val is_nil (#a:Type0) (ptr:t a)
  : SteelSel bool (llist ptr) (fun _ -> llist ptr)
          (requires fun _ -> True)
          (ensures fun h0 res h1 ->
            (res == true <==> ptr == null_llist #a) /\
            v_llist ptr h0 == v_llist ptr h1 /\
            res == Nil? (v_llist ptr h1))

val intro_llist_cons (#a:Type0) (ptr1 ptr2:t a)
  : SteelSel unit (vptr ptr1 `star` llist ptr2)
                  (fun _ -> llist ptr1)
                  (requires fun h -> next (sel ptr1 h) == ptr2)
                  (ensures fun h0 _ h1 -> v_llist ptr1 h1 == (data (sel ptr1 h0)) :: v_llist ptr2 h0)

val tail (#a:Type0) (ptr:t a)
  : SteelSel (t a) (llist ptr)
                   (fun n -> vptr ptr `star` llist n)
                   (requires fun _ -> ptr =!= null_llist)
                   (ensures fun h0 n h1 ->
                     Cons? (v_llist ptr h0) /\
                     sel ptr h1 == mk_cell n (L.hd (v_llist ptr h0)) /\
                     v_llist n h1 == L.tl (v_llist ptr h0))
