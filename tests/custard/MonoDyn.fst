module MonoDyn
open FStar.All
open FStar.IO
open FStar.Custard

class printable (a:Type) = { pr : a -> string }

instance p_int : printable int = { pr = string_of_int }
instance p_bool : printable int = { pr = (fun b -> if b = 0 then "no" else "yes") }

let render (#a:Type) {| printable a |} (x:a) : string = pr x

(* Section 3.2c: the dictionary comes out of a reference, so it is not known
   at specialization time.  [dyn] opts this call site in to passing it at run
   time -- the identity skeleton -- instead of rejecting the program.  The
   callee is unchanged and still specializes wherever the dictionary is
   known.

   Note that [dyn] has to wrap a *pure* term: F*'s ANF phase binds a whole
   effectful argument to a fresh name, marker and all, which would bury it.
   Hence the [let d = !r] below rather than [dyn !r]. *)
let from_ref (b:bool) (x:int) : ML string =
  let r = alloc p_int in
  if b then r := p_bool;
  let d = !r in
  render #int #(dyn d) x

(* The same callee, specialized as usual where the dictionary is static. *)
let static (x:int) : string = render #int #p_int x

let main () : ML unit =
  print_string (from_ref false 42);
  print_string " ";
  print_string (from_ref true 1);
  print_string " ";
  print_string (static 7);
  print_string "\n"
