module Printers.Test

open FStar.Tactics
open Printers

type t1 =
    | A : int -> int -> t1
    | B : string -> t1
    | C : t1

let t1_print : t1 -> string = synth_by_tactic printer

let _ = assert_norm (t1_print (A 5 8) = "(Printers.A 5 8)")
let _ = assert_norm (t1_print (B "thing") = "(Printers.B \"thing\")")
let _ = assert_norm (t1_print C = "Printers.C")
