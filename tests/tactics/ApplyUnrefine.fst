module ApplyUnrefine

open FStar.Tactics.V2

(* `apply` instantiates the type of the term being applied by peeling off
   arrows until it matches the goal. If what is left is a refinement (or an
   ascription) rather than an arrow, the refinement is dropped and the match
   is retried: a term of type `x:t{p}` is also a term of type `t`. *)

let posv : x:int{x > 0} = 1

(* Goal is `int`, the term has type `x:int{x > 0}`. *)
let test0 : int = _ by (apply (`posv))

let pos (u:unit) : x:int{x > 0} = 1

(* Same, with an arrow to peel off first. *)
let test1 : int = _ by (apply (`pos); exact (`()))

let pos2 (a:Type) (x:a) (u:unit) : y:int{y > 0} = 1

(* Several arrows before reaching the refinement. *)
let test2 : int = _ by (apply (`pos2); exact (`true); exact (`()))

(* Also works through an ascription. *)
let asc (u:unit) : int = (1 <: x:int{x > 0})

let test3 : int = _ by (apply (`asc); exact (`()))

(* Neither an arrow nor a refinement: still an error. *)
[@@expect_failure [228]]
let test4 : int = _ by (apply (`true))
