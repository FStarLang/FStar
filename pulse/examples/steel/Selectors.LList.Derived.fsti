module Selectors.LList.Derived

open Steel.SelEffect

open Selectors.LList
module L = FStar.List.Tot

val push (#a:Type0) (p:t a) (x: a)
  : SteelSel (t a) (llist p) (fun n -> llist n)
             (requires fun _ -> True)
             (ensures fun h0 n h1 -> v_llist n h1 == x::v_llist p h0)

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

val length (#a:Type0) (p:t a)
  : SteelSel int (llist p) (fun _ -> llist p)
             (requires fun _ -> True)
             (ensures fun h0 x h1 ->
               v_llist p h0 == v_llist p h1 /\
               L.length (v_llist p h0) == x)
