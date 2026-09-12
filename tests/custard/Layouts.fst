module Layouts
open FStar.All
open FStar.IO

(* Single constructor, single field: collapses to [int] (section 5.2). *)
type meters = | Meters of int

(* The proof field is erased, so this record collapses to its [bool] field.
   Which one survives is exactly what the layout has to record. *)
noeq type tagged = { pf: squash (1 == 1); flag: bool }

(* Every field is erased, so the type itself is erased (section 5.1). *)
noeq type proofs = { p1: squash (1 == 1); p2: squash (2 == 2) }

(* A multi-constructor variant still carries a tag, even with no fields. *)
type choice = | A | B

let name_of (c:choice) : string =
  match c with
  | A -> "A"
  | B -> "B"

(* [bound] is a ghost argument: it is deleted from the signature and from
   every call site, rather than passed as unit. *)
let scaled (n:int) (bound:FStar.Ghost.erased int) : int = n * 2

let both () : proofs = { p1 = (); p2 = () }

let main () : ML unit =
  let Meters v = Meters 42 in
  print_string (string_of_int v);
  print_string "\n";
  let t = { pf = (); flag = true } in
  print_string (if t.flag then "yes" else "no");
  print_string "\n";
  print_string (name_of A);
  print_string "\n";
  print_string (string_of_int (scaled 21 (FStar.Ghost.hide 0)));
  print_string "\n";
  let _ = both () in
  print_string "done\n"
