module FStar.BigInt

type bigint 
    = FSharp.Compatibility.OCaml.Big_int.big_int // JUST FSHARP
type t = bigint

val zero : bigint
val one : bigint
val two : bigint

val succ_big_int : (bigint -> bigint)
val pred_big_int : (bigint -> bigint)
val minus_big_int : (bigint -> bigint)
val abs_big_int : (bigint -> bigint)

val add_big_int : (bigint -> bigint -> bigint)
val mult_big_int : (bigint -> bigint -> bigint)
val sub_big_int : (bigint -> bigint -> bigint)
val div_big_int : (bigint -> bigint -> bigint)
val mod_big_int : (bigint -> bigint -> bigint)

val eq_big_int : (bigint -> bigint -> bool)
val le_big_int : (bigint -> bigint -> bool)
val lt_big_int : (bigint -> bigint -> bool)
val ge_big_int : (bigint -> bigint -> bool)
val gt_big_int : (bigint -> bigint -> bool)

val square_big_int : (bigint -> bigint)

val string_of_big_int : (bigint -> string)
val big_int_of_string : (string -> bigint)

val of_int : (int -> bigint)
val to_int : (bigint -> int)

val to_int_fs: (bigint -> int)