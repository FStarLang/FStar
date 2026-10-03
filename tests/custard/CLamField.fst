module CLamField

(* Section 6: a record whose fields are functions, built by a combinator that
   closes over its own parameter.  This is the shape of every EverParse
   bundle, and it is an honest rejection rather than a bug: the lambda
   captures [g], C has no closures, and lifting it to a top-level function
   would leave [g] unbound.

   It is here as a *named* case because [CNoClosure] captures a local let-bound
   value, and this one captures a parameter and stores the result in a
   structure -- the difference matters for the advice the diagnostic gives,
   which is to mark [g] [@@@monomorphize] so that the lambda is specialized
   away and lifted. *)

noeq type box = { fn : bool -> bool -> bool }

let mk (g: (bool -> bool)) : box = { fn = (fun x y -> g x && y) }

let idb (b: bool) : bool = b

let main () : bool = (mk idb).fn true false
