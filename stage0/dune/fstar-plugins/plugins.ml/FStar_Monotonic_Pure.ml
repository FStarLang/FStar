open Fstarcompiler
open Prims
type ('a, 'wp) is_monotonic = unit
type ('a, 'wp) as_pure_wp = 'wp
let elim_pure (f : unit -> 'a) (p : unit) : 'a= f ()
