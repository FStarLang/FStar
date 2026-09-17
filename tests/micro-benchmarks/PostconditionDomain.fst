module PostconditionDomain

(* A postcondition given by name stays an application in the result
   refinement, so its domain is checked against the result type.  One written
   as an abstraction used to be beta-reduced -- or, if trivial, dropped whole --
   before the typechecker saw it, so its binder's annotation was never looked
   at.  Both spellings are now checked. *)

let positive_post (y:pos) : prop = True

[@@expect_failure [19]]
let by_name () : Pure int (ensures positive_post) = -1

[@@expect_failure [189]]
let by_lambda (x:int) : Pure int (ensures fun (y:bool) -> True) = x

(* An annotation that *is* the result type is still erased, and the generated
   postcondition of a [Lemma] -- whose binder carries no annotation at all --
   is unaffected. *)
let same_domain (x:int) : Pure int (ensures fun (y:int) -> y == x) = x

let trivial (x:int) : Lemma (x == x) = ()

(* A result type that still has a hole in it -- [m _] below -- is not
   syntactically equal even to itself, so it must not be mistaken for a
   narrowing annotation.  Leaving a beta-redex in such a type defeats the
   syntactic matching that typeclass resolution performs: without this,
   resolving [monad] below fails with
   ‘monad (fun _ -> _: m (*?u*)_ {(fun _ -> l_True) _})’. *)
class monad (m:Type -> Type) = { ret : (#a:Type -> a -> m a) }

let hole_in_result (#m:Type -> Type) {| monad m |} (x:int) : FStar.All.ML (m _) = ret x
