module Ints

module U32 = FStar.UInt32
module I16 = FStar.Int16

let test1 (x : int) : int =
  match x with
  | 0 -> -1
  | 123 -> 321
  | 999999 -> 888888
  | x -> x-1

let test2 (x : U32.t) : U32.t =
  match x with
  | 0ul -> 1ul
  | 123ul -> 321ul
  | 999999ul -> 888888ul
  | x -> U32.sub x 1ul

let test3 (x : I16.t) : I16.t =
  match x with
  | 0s -> -1s
  | 123s -> 321s
  | 999s -> 888s
  | x -> x

(* Literals OK *)
let _ = -1073741824 (* 2^30 *)
let _ = -1073741823 (* 2^30 - 1*)
let _ = 1073741823 (* 2^30 - 1*)

(* Should be strings. *)
let _ = -1073741825 (* 2^30 + 1*)
let _ = 1073741824 (* 2^30 *)
let _ = 1073741825 (* 2^30 + 1*)
