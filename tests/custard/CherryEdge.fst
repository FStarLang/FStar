module CherryEdge
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module I128 = FStar.Int128
open FStar.All
open FStar.Dyn

(* Corner cases of the Cherry backend (cherry.md), each once a bug.  The run
   is under AddressSanitizer, so a double free or a leak fails it as surely
   as a wrong answer.  The inputs come through [hide] so that extraction
   cannot fold them. *)
let hide (#a: Type) (x: a) : ML a = x

(* A [dyn] of a plain value too big for the word: the box is counted and
   marked even though its contents are not. *)
let gd : dyn = mkdyn (3UL, 4UL)

let rec count (l: list dyn) : nat = match l with [] -> 0 | _ :: t -> 1 + count t

let dyn_pair () : ML bool =
  let d = mkdyn (hide (1UL, 2UL)) in
  let l = [d; d; gd; gd] in
  let (a, b) : U64.t & U64.t = undyn d in
  let (c, e) : U64.t & U64.t = undyn gd in
  count l = 4 && U64.v a = 1 && U64.v b = 2 && U64.v c = 3 && U64.v e = 4

(* A call through a global that holds a closure is a closure call: its
   initializer raising nothing says nothing about what the closure does. *)
exception Boom
let throw () : ML string = raise Boom
let g : unit -> ML string = hide throw
let run () : ML string = let s = g () in s ^ "!"

let global_raise () : ML bool =
  (try run () with Boom -> "caught" | e -> raise e) = "caught"

(* A constant pattern that is not a small integer is a cell, released after
   the test. *)
let big (x: int) : string =
  match x with
  | 9223372036854775808 -> "big"
  | -9223372036854775809 -> "negative"
  | 0 -> "zero"
  | _ -> "other"

let big_patterns () : ML bool =
  big (hide 9223372036854775808) = "big" &&
  big (hide (-9223372036854775809)) = "negative" &&
  big (hide 0) = "zero" && big (hide 12) = "other" &&
  big (hide 9223372036854775807) = "other"

(* Conversions between [Prims.int] and the 128-bit integers keep all 128
   bits. *)
let wide () : ML bool =
  let x : (n:int{0 <= n /\ n < pow2 128}) = hide 18446744073709551616 in
  let u = U128.uint_to_t x in
  let y : (n:int{- pow2 127 <= n /\ n < pow2 127}) = hide (-36893488147419103232) in
  let i = I128.int_to_t y in
  let z : (n:int{0 <= n /\ n < pow2 128}) = hide 5 in
  U128.v u = 18446744073709551616 && I128.v i = -36893488147419103232 &&
  U128.v (U128.uint_to_t z) = 5

(* Appending a string to itself, where it can be extended in place. *)
let self_append () : ML bool =
  let s = hide "ab" ^ hide "c" in
  let t = s ^ s in
  t = "abcabc"

let main () : ML U32.t =
  if dyn_pair () && global_raise () && big_patterns () && wide () && self_append ()
  then 0ul else 1ul
