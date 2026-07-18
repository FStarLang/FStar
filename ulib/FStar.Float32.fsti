module FStar.Float32

new
val t : Type0

inline_for_extraction
let float32 = t

val of_int : Int64.t -> t

inline_for_extraction
let zero = of_int 0L
inline_for_extraction
let one  = of_int 1L

val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val div : t -> t -> t

val lt  : t -> t -> bool
val lte : t -> t -> bool

(* IEEE 754 equality of floats. Identifies +0.0 and -0.0,
   and returns false for NaN values. This is not bit equality. *)
val ieee_eq  : t -> t -> bool

(* Bit-level equality of floats. Distinguishes +0.0 and -0.0, and,
   unlike ieee_eq, a NaN is equal to itself. *)
val bit_eq  : t -> t -> bool

(* Float literal from a string. Must be called with a concrete string;
   replaced during extraction with the corresponding C constant. *)
val of_literal : string -> t

(* String representation of a float, for debugging and tests. *)
val to_string : t -> string
