open Prims
type ('a, 'b) arrow = 'a -> 'b
type ('a, 'b) efun = 'a -> 'b
type ('a, 'b, 'f, 'g) feq = unit
let on_domain : 'a 'b . ('a -> 'b) -> 'a -> 'b = fun f -> fun x -> f x
type ('a, 'b, 'f) is_restricted = unit
type ('a, 'b) restricted_t = 'a -> 'b
type ('a, 'b) op_Hat_Subtraction_Greater = ('a, 'b) restricted_t
let on_dom : 'a 'b . ('a -> 'b) -> ('a, 'b) restricted_t =
  fun f -> fun x -> f x
let on : 'a 'b . ('a -> 'b) -> ('a, 'b) restricted_t = fun f -> fun x -> f x
type ('a, 'b) arrow_g = unit
type ('a, 'b) efun_g = unit
type ('a, 'b, 'f, 'g) feq_g = unit

type ('a, 'b, 'f) is_restricted_g = unit
type ('a, 'b) restricted_g_t = unit
type ('a, 'b) op_Hat_Subtraction_Greater_Greater = unit

