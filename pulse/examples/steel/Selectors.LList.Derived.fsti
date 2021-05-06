module Selectors.LList.Derived

open Steel.SelEffect.Atomic
open Steel.SelEffect
open Steel.SelReference

open Selectors.LList
module L = FStar.List.Tot

val push (#a:Type0) (p:t a) (x: a)
  : SteelSel (t a) (llist p) (fun n -> llist n)
             (requires fun _ -> True)
             (ensures fun h0 n h1 -> v_llist n h1 == x::v_llist p h0)

/// In place push
val ind_push (#a:Type0) (r:ref (t a)) (x: a)
  : SteelSel unit (ind_llist r) (fun _ -> ind_llist r)
             (requires fun _ -> True)
             (ensures fun h0 _ h1 -> v_ind_llist r h1 == x::v_ind_llist r h0)


//AF: Using a pair instead leads to a CheckUVar error in the implementation
// Additional problem: The projectors are not reduced, it seems the attribute it not propagated
[@@__steel_reduce__]
noeq
type res (a:Type0) = | Res: x:a -> n:t a -> res a

val pop (#a:Type0) (p:t a)
  : SteelSel (res a) (llist p) (fun res -> llist (res.n))
             (requires fun _ -> p =!= null_llist)
             (ensures fun h0 res h1 -> (
               let l = v_llist p h0 in
               Cons? l /\
               res.x == L.hd l /\
               v_llist res.n h1 == L.tl l))

/// In place pop
val ind_pop (#a:Type0) (r:ref (t a))
  : SteelSel a (ind_llist r) (fun _ -> ind_llist r)
             (requires fun h -> Cons? (v_ind_llist r h))
             (ensures fun h0 x h1 ->
               (let l = v_ind_llist r h0 in
               Cons? l /\
               x == L.hd l /\
               v_ind_llist r h1 == L.tl l)
             )

val length (#a:Type0) (p:t a)
  : SteelSel int (llist p) (fun _ -> llist p)
             (requires fun _ -> True)
             (ensures fun h0 x h1 ->
               v_llist p h0 == v_llist p h1 /\
               L.length (v_llist p h0) == x)
