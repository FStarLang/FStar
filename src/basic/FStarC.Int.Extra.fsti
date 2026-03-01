module FStarC.Int.Extra

open FStarC.Effect

(* Some extra (big) integer operations that are not there in stage0.

These should go to Prims, or somewhere in the library, and removed from
FStarC itself. *)

val logand      : int -> int -> int
val logor       : int -> int -> int
val logxor      : int -> int -> int
val lognot      : int -> int

val shift_left  : int -> int -> int
val shift_right : int -> int -> int
