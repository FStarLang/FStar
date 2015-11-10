(*--build-config
  --*)

(*
 * Uint16
 *)

module Uint16


assume val zero : uint16
(** The 16-bit integer 0. *)

assume val one : uint16
(** The 16-bit integer 1. *)

assume val max_int : uint16
(** The greatest representable 16-bit integer, 2{^16} - 1. *)

assume val min_int : uint16
(** The smallest representable 16-bit integer, 0. *)

assume val bits : int
(** The number of bits used by this integer **)

assume val add : uint16 -> uint16 -> Tot uint16
(** Addition. *)

assume val sub : uint16 -> uint16 -> Tot uint16
(** Subtraction. *)

assume val mul : uint16 -> uint16 -> Tot uint16
(** Multiplication. *)

assume val div : uint16 -> uint16 -> Tot uint16
(** Integer division.  Raise [Division_by_zero] if the second
   argument is zero.  This division rounds the real quotient of
   its arguments towards zero, as specified for {!Pervasives.(/)}. *)

assume val rem : uint16 -> uint16 -> Tot uint16
(** Integer remainder.  If [y] is not zero, the result
   of [Uint16.rem x y] satisfies the following property:
   [x = Uint16.add (Uint16.mul (Uint16.div x y) y) (Uint16.rem x y)].
   If [y = 0], [Uint16.rem x y] raises [Division_by_zero]. *)

assume val succ : uint16 -> Tot uint16
(** Successor.  [Uint16.succ x] is [Uint16.add x Uint16.one]. *)

assume val pred : uint16 -> Tot uint16
(** Predecessor.  [Uint16.pred x] is [Uint16.sub x Uint16.one]. *)

assume val abs : uint16 -> Tot uint16
(** Return the absolute value of its argument. *)

assume val neg : uint16 -> Tot uint16
(** Unary negation. *)

assume val logand : uint16 -> uint16 -> Tot uint16
(** Bitwise logical and. *)

assume val logor : uint16 -> uint16 -> Tot uint16
(** Bitwise logical or. *)

assume val logxor : uint16 -> uint16 -> Tot uint16
(** Bitwise logical exclusive or. *)

assume val lognot : uint16 -> Tot uint16
(** Bitwise logical negation *)

assume val shift_left : uint16 -> int -> Tot uint16
(** [Uint16.shift_left x y] shifts [x] to the left by [y] bits.
   The result is unspecified if [y < 0] or [y >= 16]. *)

assume val shift_right : uint16 -> int -> Tot uint16
(** [Uint16.shift_right x y] shifts [x] to the right by [y] bits.
   This is an arithmetic shift: the sign bit of [x] is replicated
   and inserted in the vacated bits.
   The result is unspecified if [y < 0] or [y >= 16]. *)

assume val shift_right_logical : uint16 -> int -> Tot uint16
(** [Uint16.shift_right_logical x y] shifts [x] to the right by [y] bits.
   This is a logical shift: zeroes are inserted in the vacated bits
   regardless of the sign of [x].
   The result is unspecified if [y < 0] or [y >= 16]. *)

assume val of_int : int -> Tot uint16
(** Convert the given integer (type [int]) to a 16-bit integer
    (type [uint16]). *)

assume val to_int : uint16 -> Tot int
(** Convert the given 16-bit integer (type [uint16]) to an
   integer (type [int]).  On 16-bit platforms, the 16-bit integer
   is taken modulo 2{^16}, i.e. the high-order bit is lost
   during the conversion.  On 64-bit platforms, the conversion
   is exact. *)

assume val of_string : string -> Tot uint16
(** Convert the given string to a 16-bit integer.
   The string is read in decimal (by default) or in hexadecimal,
   octal or binary if the string begins with [0x], [0o] or [0b]
   respectively.
   Raise [Failure "int_of_string"] if the given string is not
   a valid representation of an integer, or if the integer represented
   exceeds the range of integers representable in type [uint16]. *)

assume val to_string : uint16 -> Tot string
(** Return the string representation of its argument, in signed decimal. *)

assume val compare : uint16 -> uint16 -> Tot int
(** The comparison function for integers of type uint16. **)
