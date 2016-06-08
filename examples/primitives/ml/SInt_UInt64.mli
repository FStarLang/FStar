type uint64
type uint128

type limb = uint64
type wide = uint128
       
val n:int

val zero:uint64
val one:uint64
val ones:uint64

val zero_wide:uint128
val one_wide:uint128
val ones_wide:uint128

val add: uint64 -> uint64 -> uint64
val add_mod: uint64 -> uint64 -> uint64
val sub: uint64 -> uint64 -> uint64
val sub_mod:uint64 -> uint64 -> uint64
val mul:uint64 -> uint64 -> uint64
val mul_mod:uint64 -> uint64 -> uint64
val div:uint64 -> uint64 -> uint64
val rem:uint64 -> uint64 -> uint64

val logand:uint64 -> uint64 -> uint64
val logxor:uint64 -> uint64 -> uint64
val logor:uint64 -> uint64 -> uint64
val lognot:uint64 -> uint64

val shift_left:uint64 -> int -> uint64
val shift_right:uint64 -> int -> uint64

val rotate_left:uint64 -> int -> uint64
val rotate_right:uint64 -> int -> uint64

val op_Hat_Plus: uint64 -> uint64 -> uint64
val op_Hat_Subtraction: uint64 -> uint64 -> uint64
val op_Hat_Star: uint64 -> uint64 -> uint64
val op_Hat_Plus_Percent: uint64 -> uint64 -> uint64
val op_Hat_Subtraction_Percent: uint64 -> uint64 -> uint64
val op_Hat_Star_Percent: uint64 -> uint64 -> uint64
val op_Hat_Slash:uint64 -> uint64 -> uint64
val op_Hat_Less_Less:uint64 -> int -> uint64
val op_Hat_Greater_Greater:uint64 -> int -> uint64
val op_Hat_Amp:uint64 -> uint64 -> uint64
val op_Hat_Bar:uint64 -> uint64 -> uint64
val op_Hat_Hat:uint64 -> uint64 -> uint64

val op_Hat_Star_Hat: uint64 -> uint64 -> uint128
                  
val op_Hat_Hat_Plus: uint128 -> uint128 -> uint128
val op_Hat_Hat_Plus_Percent: uint128 -> uint128 -> uint128
val op_Hat_Hat_Subtraction: uint128 -> uint128 -> uint128
val op_Hat_Hat_Subtraction_Percent: uint128 -> uint128 -> uint128
val op_Hat_Hat_Star: uint128 -> uint128 -> uint128
val op_Hat_Hat_Star_Percent: uint128 -> uint128 -> uint128
val op_Hat_Hat_Less_Less:uint128 -> int -> uint128
val op_Hat_Hat_Greater_Greater:uint128 -> int -> uint128
val op_Hat_Hat_Amp:uint128 -> uint128 -> uint128
val op_Hat_Hat_Bar:uint128 -> uint128 -> uint128
val op_Hat_Hat_Hat:uint128 -> uint128 -> uint128

val of_int: int -> uint64
(* val of_int64: int64 -> uint64 *)
val of_string: string -> uint64
val uint128_of_int: int -> uint128
val uint128_of_string: string -> uint128
                        
val eq:uint64 -> uint64 -> uint64
val gte:uint64 -> uint64 -> uint64

(* Only for realization purposes, does not exists in F* library *)
val to_string: uint64 -> string
val to_int: uint64 -> int
(* val to_int64: uint64 -> int64 *)
val uint128_to_string: uint128 -> string
val uint128_to_int: uint128 -> int
