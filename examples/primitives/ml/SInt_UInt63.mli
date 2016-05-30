type uint63
type native_int = uint63

val n:int

val zero:uint63
val one:uint63
val ones:uint63

val add: uint63 -> uint63 -> uint63
val add_mod: uint63 -> uint63 -> uint63
val sub: uint63 -> uint63 -> uint63
val sub_mod:uint63 -> uint63 -> uint63
val mul:uint63 -> uint63 -> uint63
val mul_mod:uint63 -> uint63 -> uint63
val div:uint63 -> uint63 -> uint63
val rem:uint63 -> uint63 -> uint63

val logand:uint63 -> uint63 -> uint63
val logxor:uint63 -> uint63 -> uint63
val logor:uint63 -> uint63 -> uint63
val lognot:uint63 -> uint63

val shift_left:uint63 -> int -> uint63
val shift_right:uint63 -> int -> uint63

val rotate_left:uint63 -> int -> uint63
val rotate_right:uint63 -> int -> uint63

val op_Hat_Plus: uint63 -> uint63 -> uint63
val op_Hat_Subtraction: uint63 -> uint63 -> uint63
val op_Hat_Star: uint63 -> uint63 -> uint63
val op_Hat_Slash:uint63 -> uint63 -> uint63
val op_Hat_Less_Less:uint63 -> int -> uint63
val op_Hat_Greater_Greater:uint63 -> int -> uint63
val op_Hat_Amp:uint63 -> uint63 -> uint63
val op_Hat_Bar:uint63 -> uint63 -> uint63
val op_Hat_Hat:uint63 -> uint63 -> uint63

val of_int: int -> uint63
val of_string: string -> uint63
                        
val eq:uint63 -> uint63 -> uint63
val gte:uint63 -> uint63 -> uint63

(* Only for realization purposes, does not exists in F* library *)
val to_int: uint63 -> int
val to_string: uint63 -> string
