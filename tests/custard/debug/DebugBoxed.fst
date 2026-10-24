module DebugBoxed

(* The same for a boxed (recursive) type, whose field is a pointer. *)
open FStar.All

type e = | Num : n:int -> e | Add : l:e -> r:e -> e

let main () : ML FStar.UInt32.t =
  let r = alloc (Num 1) in
  match Add?.l !r with
  | Num n -> if n = 1 then 0ul else 1ul
  | _ -> 1ul
