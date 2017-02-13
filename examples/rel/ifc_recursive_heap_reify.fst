module Ifc_Recursive_Heap_Reify

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel

(* reifiable val p1 : hi:id -> *)
(*   IntStore unit *)
(*   (requires (fun h -> hi = hi)) *)
(*   (ensures  (fun h1 _ h2 -> True)) *)
reifiable let rec p1 hi  : IntStore unit (requires (fun h -> hi = hi)) (ensures (fun h1 _ h2 -> True)) = ()


(*

reifiable val p1 (lo hi :id ): gh:heap ->
  IntStore unit
  (requires (fun h -> h == gh))
  (ensures  (fun h1 _ h2 -> True))
  (decreases (sel gh hi))
reifiable let rec p1 lo hi gh  =
  if (read hi) > 0 then
    (write hi (read hi - 1);
    p1 lo hi (IS?.get ()))

*)
