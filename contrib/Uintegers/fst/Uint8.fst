(*--build-config
  --*)

(*
 * Uint8
 *)

module Uint8


assume val zero : uint8
(** The 8-bit integer 0. *)

assume val one : uint8
(** The 8-bit integer 1. *)

assume val max_int : uint8
(** The greatest representable 8-bit integer, 2{^8} - 1. *)

assume val min_int : uint8
(** The smallest representable 8-bit integer, 0. *)

assume val bits : int
(** The number of bits used by this integer **)

assume val add : uint8 -> uint8 -> Tot uint8
(** Addition. *)

assume val sub : uint8 -> uint8 -> Tot uint8
(** Subtraction. *)

assume val mul : uint8 -> uint8 -> Tot uint8
(** Multiplication. *)

assume val div : uint8 -> uint8 -> Tot uint8
(** Integer division.  Raise [Division_by_zero] if the second
   argument is zero.  This division rounds the real quotient of
   its arguments towards zero, as specified for {!Pervasives.(/)}. *)

assume val rem : uint8 -> uint8 -> Tot uint8
(** Integer remainder.  If [y] is not zero, the result
   of [Uint8.rem x y] satisfies the following property:
   [x = Uint8.add (Uint8.mul (Uint8.div x y) y) (Uint8.rem x y)].
   If [y = 0], [Uint8.rem x y] raises [Division_by_zero]. *)

assume val succ : uint8 -> Tot uint8
(** Successor.  [Uint8.succ x] is [Uint8.add x Uint8.one]. *)

assume val pred : uint8 -> Tot uint8
(** Predecessor.  [Uint8.pred x] is [Uint8.sub x Uint8.one]. *)

assume val abs : uint8 -> Tot uint8
(** Return the absolute value of its argument. *)

assume val neg : uint8 -> Tot uint8
(** Unary negation. *)

assume val logand : uint8 -> uint8 -> Tot uint8
(** Bitwise logical and. *)

assume val logor : uint8 -> uint8 -> Tot uint8
(** Bitwise logical or. *)

assume val logxor : uint8 -> uint8 -> Tot uint8
(** Bitwise logical exclusive or. *)

assume val lognot : uint8 -> Tot uint8
(** Bitwise logical negation *)

assume val shift_left : uint8 -> int -> Tot uint8
(** [Uint8.shift_left x y] shifts [x] to the left by [y] bits.
   The result is unspecified if [y < 0] or [y >= 8]. *)

assume val shift_right : uint8 -> int -> Tot uint8
(** [Uint8.shift_right x y] shifts [x] to the right by [y] bits.
   This is an arithmetic shift: the sign bit of [x] is replicated
   and inserted in the vacated bits.
   The result is unspecified if [y < 0] or [y >= 8]. *)

assume val shift_right_logical : uint8 -> int -> Tot uint8
(** [Uint8.shift_right_logical x y] shifts [x] to the right by [y] bits.
   This is a logical shift: zeroes are inserted in the vacated bits
   regardless of the sign of [x].
   The result is unspecified if [y < 0] or [y >= 8]. *)

assume val of_int : int -> Tot uint8
(** Convert the given integer (type [int]) to a 8-bit integer
    (type [uint8]). *)

assume val to_int : uint8 -> Tot int
(** Convert the given 8-bit integer (type [uint8]) to an
   integer (type [int]).  On 8-bit platforms, the 8-bit integer
   is taken modulo 2{^8}, i.e. the high-order bit is lost
   during the conversion.  On 64-bit platforms, the conversion
   is exact. *)

assume val of_string : string -> Tot uint8
(** Convert the given string to a 8-bit integer.
   The string is read in decimal (by default) or in hexadecimal,
   octal or binary if the string begins with [0x], [0o] or [0b]
   respectively.
   Raise [Failure "int_of_string"] if the given string is not
   a valid representation of an integer, or if the integer represented
   exceeds the range of integers representable in type [uint8]. *)

assume val to_string : uint8 -> Tot string
(** Return the string representation of its argument, in signed decimal. *)

assume val compare : uint8 -> uint8 -> Tot int
(** The comparison function for integers of type uint8. **)
