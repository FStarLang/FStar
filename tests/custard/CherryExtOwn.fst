module CherryExtOwn

(* cherry.md, "Calling convention": an external borrows its arguments unless
   a binder says [@@@cherry_owned].  Both stubs read the string; the owned one
   also releases it.  ASan catches either mistake: a double free if the
   attribute were ignored, a leak if borrowing were taken as owning. *)

module U32 = FStar.UInt32
open FStar.All
open FStar.Attributes

[@@custard_extern "ext_len_borrowed"; custard_c_header "CherryExtOwn_stubs.h"]
assume val len_b : string -> ML U32.t

[@@custard_extern "ext_len_owned"; custard_c_header "CherryExtOwn_stubs.h"]
assume val len_o : ([@@@cherry_owned] s: string) -> U32.t -> ML U32.t

let rec grow (n: nat) (s: string) : ML string =
  if n = 0 then s else grow (n - 1) (s ^ "a")

let main () : ML U32.t =
  let s = grow 8 "" in
  let a = len_b s in
  let b = len_o s 1ul in
  let c = len_b s in
  if a = 8ul && b = 9ul && c = 8ul then 0ul else 1ul
