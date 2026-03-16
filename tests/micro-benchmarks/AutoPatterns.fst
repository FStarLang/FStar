module AutoPatterns

(* Test automatic SMT pattern inference for quantifiers.
   Run with --ext auto_patterns *)

(* Simple uninterpreted functions for testing *)
assume val f : int -> int
assume val g : int -> int
assume val h : int -> int -> int
assume val k : int -> int -> int -> int

(* Test 1: Basic inference — single variable, two candidate terms *)
(* forall x. f(x) == h(g(x), 0) should infer {:pattern (f x) \/ (g x)} *)
assume val ax1 : squash (forall (x:int). f x == g x)

(* Test 2: Multi-variable, single covering term *)
(* forall x y. h(f(x), g(y)) should infer {:pattern (h (f x) (g y))} *)
assume val ax2 : squash (forall (x:int) (y:int). h (f x) (g y) == 0)

(* Test 3: Single variable, multiple disjunctive candidates *)
(* forall x. h(f(x), g(x)) should infer {:pattern (f x) \/ (g x)} *)
assume val ax3 : squash (forall (x:int). h (f x) (g x) == 0)

(* Test 4: User-supplied pattern should be preserved *)
assume val ax4 : squash (forall (x:int). {:pattern (f x)} f x == g x)

(* Test 5: exists should also work *)
assume val ax5 : squash (exists (x:int). f x == 0)

(* A simple test that exercises the inferred patterns *)
let test1 () : Lemma (f 42 == g 42) = ()
