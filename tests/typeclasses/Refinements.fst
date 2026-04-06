module Refinements

open FStar.Tactics.Typeclasses { solve }

type dummy (tag : int) (x : Type) = | C

class cc (x : Type) = {
  foo : x;
  meta : int;
}

type natlt (x:nat) = y:nat{y < x}

(* using a refinement on z *)
instance inst_1_1 (z : int{z > 0}) : cc (dummy 1 (natlt z)) = { foo = C; meta = 42; }

(* no instance with tag=0 *)
[@@expect_failure [228]]
let _ : dummy 0 (natlt 0) = foo

(* fine *)
let _ : dummy 1 (natlt 1) = foo

(* 0 < 0 fails *)
[@@expect_failure [19]]
let _ : dummy 1 (natlt 0) = foo

(* a separate squash on z *)
instance inst_2_1 (z : int) (_ : squash (z > 0)) : cc (dummy 2 (natlt z)) = { foo = C; meta = 42; }

(* fine *)
let _ : dummy 2 (natlt 1) = foo

(* 0 < 0 fails *)
[@@expect_failure [19]]
let _ : dummy 2 (natlt 0) = foo

(* a separate unit refinement *)
instance inst_3_1 (z : int) (_ : unit {z > 0}) : cc (dummy 3 (natlt z)) = { foo = C; meta = 42; }

(* fine *)
let _ : dummy 3 (natlt 1) = foo

(* 0 < 0 fails *)
[@@expect_failure [19]]
let _ : dummy 3 (natlt 0) = foo


type box t = | Box of t

(* a refinement on the type, not on the value *)

instance refinement_on_subgoal (t : Type) (d : cc t { d.meta == 1 }) : cc (box t) = { foo = Box d.foo; meta = 1; }

instance inst_4_string : cc (dummy 4 string) = { foo = C; meta = 1; }
instance inst_4_bool   : cc (dummy 4 bool) = { foo = C; meta = 42; }

let _ : box (dummy 4 string) = foo

(* Typeclass instantiation will still try to apply the instance, not looking at
   the refinement, which will later fail. *)
[@@expect_failure [19]]
let _ : box (dummy 4 bool) = foo


(* F* rejects this instance, claiming the resultl type is not a class. *)
// instance inst_4_unit () : Tot (inst : cc (dummy 4 unit) { inst.meta == 45}) = { foo = C; meta = 45; }



class dummy2 = {
  x:unit;
}

assume val p : prop

instance blah (_ : squash p) : dummy2 = { x = (); }

let test (_ : squash p) : dummy2 = solve

[@@expect_failure [19]]
let test_fail () : dummy2 = solve
