module ImplicitArrowDefensive

(* An implicit created under local binders is abstracted over them, so its type
   is [bs -> squash phi] rather than [squash phi].
   [Rel.try_solve_single_valued_implicits] eta-expands the unit solution for
   such an implicit, and [arrow_formals_comp] *opens* [bs] -- so the codomain it
   then looks at has to be looked at with [bs] in scope.  Normalizing it in the
   unextended environment is what [--defensive error] catches, as Error 290.

   This file is checked with [--defensive error]; see the Makefile. *)

let needs (#proof:(x:int -> squash (x == x))) (x:int) : Tot int = x

let run : int = needs 0
