module LocalFunDup
open FStar.All

(* A monomorphic local function called once in each of several branches.
   Under Cherry it is a closure, not a copy per branch: [marker] is called
   from exactly one place in the C. *)

let marker () : ML unit = FStar.IO.print_string "helper\n"

let f (x:int) (b:bool) : ML int =
  let helper (y:int) : ML int =
    marker ();
    y + x
  in
  match x, b with
  | 0, _ -> 0
  | _, true -> helper 1
  | 1, false -> helper 2
  | _ -> if x > 3 then helper 3 else helper 4

let main () : ML unit =
  FStar.IO.print_string (string_of_int (f 7 true + f 1 false + f 4 false + f 2 true));
  FStar.IO.print_string "\n"
