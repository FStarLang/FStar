module TcCache

(* Tests for the caching of typeclass resolution. *)

open FStar.Tactics.Typeclasses
open FStar.Ghost

class c (a:Type) = { v : int }

instance c_int : c int = { v = 1 }

let _ = assert (v #int == 1)
let _ = assert (v #int == 1)

(* A local instance invalidates the cache, and is preferred. *)
let t1 (d : c int) : int = v #int
let _ = assert (forall (d : c int). t1 d == d.v)

(* Outside of its scope, the global instance is used again. *)
let _ = assert (v #int == 1)

(* A failure is cached too, but adding an instance invalidates the cache. *)
[@@expect_failure [228]]
let _ = v #bool
[@@expect_failure [228]]
let _ = v #bool

instance c_bool : c bool = { v = 2 }

let _ = assert (v #bool == 2)

(* A local instance is pushed with its type: a binder whose type is still a
   uvar when it is pushed is not a local instance. *)
[@@expect_failure [228]]
let t2 = fun d -> (v #string <: int) + (d <: c string).v

let t3 = fun (d : c string) -> v #string

(* The cache key does not contain the functional dependencies: both uses
   below resolve [has_pts_to (ref bool) _], and get the same instance. *)
[@@fundeps [1]]
class has_pts_to (p x : Type) = {
  pts_to : p -> x -> prop;
}

assume val ref : Type0 -> Type0

instance has_pts_to_ref (x : Type) : has_pts_to (ref x) x = {
  pts_to = (fun r x -> True);
}

let t4 (r : ref bool) (b : bool) (eb : erased bool) : GTot prop =
  pts_to r b /\ pts_to r eb
