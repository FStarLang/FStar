module TypeclassRefinedResult

(* A typeclass-constrained variable that has both a lower bound and a
   *refined* upper bound must be solved from its lower bounds: an instance
   head never mentions a refinement, so committing the variable to the
   refined upper bound makes the constraint unsolvable.

   Here [(++)]'s implicit [a] is bounded below by [int] (the type of its
   arguments) and above by [y:int{y >= 0}] (the function's result type).
   Solving it from the upper bound leaves [c0 (y:int{y >= 0})], which no
   instance matches. *)

class c0 (a:Type) = { op : a -> a -> a }

instance c0_int : c0 int = { op = (fun x y -> x + y) }

let ( ++ ) #a {| c0 a |} (x y : a) : a = op #a x y

let f (x:int) : y:int{y >= 0} = (if x >= 0 then x else 0) ++ 0

(* The same thing with the refinement coming from an [ensures] clause rather
   than written out, which is how it turns up in practice. *)
let g (x:int) : Pure int (requires True) (ensures fun y -> y >= 0) =
  (if x >= 0 then x else 0) ++ 0
