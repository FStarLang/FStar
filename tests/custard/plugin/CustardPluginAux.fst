module CustardPluginAux

(* Section 13.4: `RegEmb` generates a registration only for a module named by
   `--custard_entry`.  A `[@@plugin]` that lives anywhere else is extracted --
   it is reachable, so it is requested -- but nothing registers it, and the
   failure surfaces at run time, arbitrarily far from the cause, as "Tactic got
   stuck!  Reduction stopped at: ...".  So a plugin's *every* module carrying
   the attribute has to be a root, not just the one that names the others.

   Nothing in CustardPlugin refers to this module: it is a second root, and
   the point of the test is that a second root is what it takes. *)

[@@plugin]
irreducible
let aux (x:int) : int = x * 100
