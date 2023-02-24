open Prims
type ('a, 'wp) is_monotonic = unit
type ('a, 'wp) as_pure_wp = 'wp
let elim_pure : 'a 'wp . (unit -> 'a) -> unit -> 'a = fun f -> fun p -> f ()