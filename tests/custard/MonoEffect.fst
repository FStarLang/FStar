module MonoEffect
open FStar.All
open FStar.IO
open FStar.Attributes

class printable (a:Type) = { pr : a -> string }

instance p_int : printable int = { pr = string_of_int }

let render (#a:Type) {| printable a |} (x:a) : string = pr x

(* A dictionary read out of a reference is not a compile-time value at all:
   the dereference runs when the program runs.  This is the shape
   FStarC.Syntax.VisitM.tie_bu is written in, where a recursive typeclass
   instance is tied through a mutable cell. *)
let main () : ML unit =
  let r : ref (printable int) = alloc p_int in
  let d = !r in
  print_string (render #int #d 42)
