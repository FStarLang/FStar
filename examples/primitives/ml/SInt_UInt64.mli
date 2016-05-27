type uint64

val n:int

val zero:uint64
val one:uint64
val ones:uint64

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
val op_Hat_Slash:uint64 -> uint64 -> uint64
val op_Hat_Less_Less:uint64 -> int -> uint64
val op_Hat_Greater_Greater:uint64 -> int -> uint64
val op_Hat_Amp:uint64 -> uint64 -> uint64
val op_Hat_Bar:uint64 -> uint64 -> uint64
val op_Hat_Hat:uint64 -> uint64 -> uint64

val of_int: int -> uint64
val of_string: string -> uint64
                        
val eq:uint64 -> uint64 -> uint64
val gte:uint64 -> uint64 -> uint64

(* Only for realization purposes, does not exists in F* library *)
val to_string: uint64 -> string
val to_int: uint64 -> int
