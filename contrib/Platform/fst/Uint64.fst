(*--build-config
  --*)

(*
 * Uint64
 *)

module Uint64


assume val zero : uint64
(** The 64-bit integer 0. *)

assume val one : uint64
(** The 64-bit integer 1. *)

assume val max_int : uint64
(** The greatest representable 64-bit integer, 2{^64} - 1. *)

assume val min_int : uint64
(** The smallest representable 64-bit integer, 0. *)

assume val bits : int
(** The number of bits used by this integer **)

assume val add : uint64 -> uint64 -> Tot uint64
(** Addition. *)

assume val sub : uint64 -> uint64 -> Tot uint64
(** Subtraction. *)

assume val mul : uint64 -> uint64 -> Tot uint64
(** Multiplication. *)

assume val div : uint64 -> uint64 -> Tot uint64
(** Integer division.  Raise [Division_by_zero] if the second
   argument is zero.  This division rounds the real quotient of
   its arguments towards zero, as specified for {!Pervasives.(/)}. *)

assume val rem : uint64 -> uint64 -> Tot uint64
(** Integer remainder.  If [y] is not zero, the result
   of [Uint64.rem x y] satisfies the following property:
   [x = Uint64.add (Uint64.mul (Uint64.div x y) y) (Uint64.rem x y)].
   If [y = 0], [Uint64.rem x y] raises [Division_by_zero]. *)

assume val succ : uint64 -> Tot uint64
(** Successor.  [Uint64.succ x] is [Uint64.add x Uint64.one]. *)

assume val pred : uint64 -> Tot uint64
(** Predecessor.  [Uint64.pred x] is [Uint64.sub x Uint64.one]. *)

assume val abs : uint64 -> Tot uint64
(** Return the absolute value of its argument. *)

assume val neg : uint64 -> Tot uint64
(** Unary negation. *)

assume val logand : uint64 -> uint64 -> Tot uint64
(** Bitwise logical and. *)

assume val logor : uint64 -> uint64 -> Tot uint64
(** Bitwise logical or. *)

assume val logxor : uint64 -> uint64 -> Tot uint64
(** Bitwise logical exclusive or. *)

assume val lognot : uint64 -> Tot uint64
(** Bitwise logical negation *)

assume val shift_left : uint64 -> int -> Tot uint64
(** [Uint64.shift_left x y] shifts [x] to the left by [y] bits.
   The result is unspecified if [y < 0] or [y >= 64]. *)

assume val shift_right : uint64 -> int -> Tot uint64
(** [Uint64.shift_right x y] shifts [x] to the right by [y] bits.
   This is an arithmetic shift: the sign bit of [x] is replicated
   and inserted in the vacated bits.
   The result is unspecified if [y < 0] or [y >= 64]. *)

assume val shift_right_logical : uint64 -> int -> Tot uint64
(** [Uint64.shift_right_logical x y] shifts [x] to the right by [y] bits.
   This is a logical shift: zeroes are inserted in the vacated bits
   regardless of the sign of [x].
   The result is unspecified if [y < 0] or [y >= 64]. *)

assume val of_int : int -> Tot uint64
(** Convert the given integer (type [int]) to a 64-bit integer
    (type [uint64]). *)

assume val to_int : uint64 -> Tot int
(** Convert the given 64-bit integer (type [uint64]) to an
   integer (type [int]).  On 64-bit platforms, the 64-bit integer
   is taken modulo 2{^64}, i.e. the high-order bit is lost
   during the conversion.  On 64-bit platforms, the conversion
   is exact. *)

assume val of_string : string -> Tot uint64
(** Convert the given string to a 64-bit integer.
   The string is read in decimal (by default) or in hexadecimal,
   octal or binary if the string begins with [0x], [0o] or [0b]
   respectively.
   Raise [Failure "int_of_string"] if the given string is not
   a valid representation of an integer, or if the integer represented
   exceeds the range of integers representable in type [uint64]. *)

assume val to_string : uint64 -> Tot string
(** Return the string representation of its argument, in signed decimal. *)

assume val compare : uint64 -> uint64 -> Tot int
(** The comparison function for integers of type uint64. **)
