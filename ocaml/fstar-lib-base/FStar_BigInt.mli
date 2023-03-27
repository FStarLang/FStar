type bigint
type t = bigint

val zero : bigint
val one: bigint
val two: bigint

val succ_big_int: bigint -> bigint
val pred_big_int: bigint -> bigint
val minus_big_int: bigint -> bigint
val abs_big_int: bigint -> bigint

val add_big_int: bigint -> bigint -> bigint
val mult_big_int: bigint -> bigint -> bigint
val sub_big_int: bigint -> bigint -> bigint
val div_big_int: bigint -> bigint -> bigint
val mod_big_int: bigint -> bigint -> bigint

(* Euclidean division *)
val ediv_big_int: bigint -> bigint -> bigint
val erem_big_int: bigint -> bigint -> bigint

val eq_big_int: bigint -> bigint -> bool
val le_big_int: bigint -> bigint -> bool
val lt_big_int: bigint -> bigint -> bool
val ge_big_int: bigint -> bigint -> bool
val gt_big_int: bigint -> bigint -> bool

val logand_big_int: bigint -> bigint -> bigint
val logor_big_int: bigint -> bigint -> bigint
val logxor_big_int: bigint -> bigint -> bigint
val lognot_big_int: bigint -> bigint

val shift_left_big_int: bigint -> bigint -> bigint
val shift_right_big_int: bigint -> bigint -> bigint
val shift_arithmetic_left_big_int: bigint -> int -> bigint
val shift_arithmetic_right_big_int: bigint -> int -> bigint

val sqrt_big_int: bigint -> bigint

val of_int: int -> bigint
val to_int: bigint -> int

(* These should be identity functions, because prims.ml chose to define int as bigint.
   But OCaml does not allow implementations in .mli
   This may not hold for other backends
*)
val of_int_fs: bigint -> bigint
val to_int_fs: bigint -> bigint

val big_int_of_string: string -> bigint
val string_of_big_int: bigint -> string

val of_hex: string -> bigint

val pp_print: Format.formatter -> t -> unit

(* Needed by FStar_Compiler_Util.time_diff *)
val of_float: float -> bigint

(* Needed by FStar_Compiler_Util.sleep *)
val to_float: bigint -> float

(* Needed by FStar_Date.seconds_from_dawn *)
val of_int64: int64 -> bigint

(* Needed by FStar_Bytes.bytes_of_int *)
val to_int64: bigint -> int64

(* Needed by FStar_Compiler_Util.ZHashTbl *)
module HashedType: BatHashtbl.HashedType with type t = t

(* Needed by FStar_Compiler_Util.ZMap *)
module OrderedType: BatInterfaces.OrderedType with type t = t

(* Which bigint implementation are we using? Shown with --version *)
val flavor: string

(* Karamel integers. See comments in FStar.BigInt.fsti *)
type krmlint = int
val krmlint_of_int_fs : t -> krmlint
