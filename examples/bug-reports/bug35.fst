module Bug35
open Prims.PURE

val index : l : list 'a -> n:int -> Tot bool
let rec index l n =
  match l with
  | [] -> false
  | h :: t -> if n = 0 then true else index t (n-1)
