(*--build-config
  --*)

(*
 * Uint32
 *)

module Uint32


assume val zero : uint32
(** The 32-bit integer 0. *)

assume val one : uint32
(** The 32-bit integer 1. *)

assume val max_int : uint32
(** The greatest representable 32-bit integer, 2{^32} - 1. *)

assume val min_int : uint32
(** The smallest representable 32-bit integer, 0. *)

assume val bits : int
(** The number of bits used by this integer **)

assume val add : uint32 -> uint32 -> Tot uint32
(** Addition. *)

assume val sub : uint32 -> uint32 -> Tot uint32
(** Subtraction. *)

assume val mul : uint32 -> uint32 -> Tot uint32
(** Multiplication. *)

assume val div : uint32 -> uint32 -> Tot uint32
(** Integer division.  Raise [Division_by_zero] if the second
   argument is zero.  This division rounds the real quotient of
   its arguments towards zero, as specified for {!Pervasives.(/)}. *)

assume val rem : uint32 -> uint32 -> Tot uint32
(** Integer remainder.  If [y] is not zero, the result
   of [Uint32.rem x y] satisfies the following property:
   [x = Uint32.add (Uint32.mul (Uint32.div x y) y) (Uint32.rem x y)].
   If [y = 0], [Uint32.rem x y] raises [Division_by_zero]. *)

assume val succ : uint32 -> Tot uint32
(** Successor.  [Uint32.succ x] is [Uint32.add x Uint32.one]. *)

assume val pred : uint32 -> Tot uint32
(** Predecessor.  [Uint32.pred x] is [Uint32.sub x Uint32.one]. *)

assume val abs : uint32 -> Tot uint32
(** Return the absolute value of its argument. *)

assume val neg : uint32 -> Tot uint32
(** Unary negation. *)

assume val logand : uint32 -> uint32 -> Tot uint32
(** Bitwise logical and. *)

assume val logor : uint32 -> uint32 -> Tot uint32
(** Bitwise logical or. *)

assume val logxor : uint32 -> uint32 -> Tot uint32
(** Bitwise logical exclusive or. *)

assume val lognot : uint32 -> Tot uint32
(** Bitwise logical negation *)

assume val shift_left : uint32 -> int -> Tot uint32
(** [Uint32.shift_left x y] shifts [x] to the left by [y] bits.
   The result is unspecified if [y < 0] or [y >= 32]. *)

assume val shift_right : uint32 -> int -> Tot uint32
(** [Uint32.shift_right x y] shifts [x] to the right by [y] bits.
   This is an arithmetic shift: the sign bit of [x] is replicated
   and inserted in the vacated bits.
   The result is unspecified if [y < 0] or [y >= 32]. *)

assume val shift_right_logical : uint32 -> int -> Tot uint32
(** [Uint32.shift_right_logical x y] shifts [x] to the right by [y] bits.
   This is a logical shift: zeroes are inserted in the vacated bits
   regardless of the sign of [x].
   The result is unspecified if [y < 0] or [y >= 32]. *)

assume val of_int : int -> Tot uint32
(** Convert the given integer (type [int]) to a 32-bit integer
    (type [uint32]). *)

assume val to_int : uint32 -> Tot int
(** Convert the given 32-bit integer (type [uint32]) to an
   integer (type [int]).  On 32-bit platforms, the 32-bit integer
   is taken modulo 2{^32}, i.e. the high-order bit is lost
   during the conversion.  On 64-bit platforms, the conversion
   is exact. *)

assume val of_string : string -> Tot uint32
(** Convert the given string to a 32-bit integer.
   The string is read in decimal (by default) or in hexadecimal,
   octal or binary if the string begins with [0x], [0o] or [0b]
   respectively.
   Raise [Failure "int_of_string"] if the given string is not
   a valid representation of an integer, or if the integer represented
   exceeds the range of integers representable in type [uint32]. *)

assume val to_string : uint32 -> Tot string
(** Return the string representation of its argument, in signed decimal. *)

assume val compare : uint32 -> uint32 -> Tot int
(** The comparison function for integers of type uint32. **)
