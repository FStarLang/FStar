module FStar.Util

open FStar.Heap
open FStar.HyperStack

(* 2016-11-22: the following MUST be defined here AFTER the above `open',
   since they are used in [op_At_Plus_At] below *)
let op_Plus_Plus x y = TSet.union x y
let op_Plus_Plus_Hat x y = x ++ (TSet.singleton y)
let op_Hat_Plus_Hat  x y = (TSet.singleton x) ++ (TSet.singleton y)

let op_At_Plus_At (#a:Type) (#b:Type) (x:reference a) (y:reference b) =
   Set.union (Set.singleton (as_addr x)) (Set.singleton (as_addr y))
let op_Plus_Plus_At (#a:Type) (x:Set.set nat) (y:reference a) = Set.union x (Set.singleton (as_addr y))
