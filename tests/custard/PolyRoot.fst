module PolyRoot

(* Section 72.1.  [--custard_entry_module] roots every definition a module
   defines.  [pick] is polymorphic, and specialization takes its type argument
   from a call site -- which a root, by definition, does not have.  Rooting it
   would reach the C backend with a type variable still standing and be
   refused with error 368, naming a definition the user never asked to
   compile.

   So it is not rooted.  [use_it] is, and the instance it calls is what comes
   out.  Kuiper's whole-module sweep found this: six of their modules were
   refused for a polymorphic helper that the program only ever calls at
   concrete types. *)

module U32 = FStar.UInt32

let pick (#a:Type0) (b:bool) (x y : a) : a = if b then x else y

let use_it (x y : U32.t) : U32.t = pick true x y

(* A specification is skipped for the same reason and by the same loop; the
   two are on one footing. *)
let spec (n:nat) : GTot nat = n + 1

let main () : FStar.All.ML FStar.Int32.t =
  if use_it 6ul 7ul = 6ul then 0l else 1l
