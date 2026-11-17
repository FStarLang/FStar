module CherryUnboxedUpdate

(* An update of an unboxed record moves the fields it keeps out of the old
   one, and the fields the new values read, when the old one dies there. *)

open FStar.All

type r = { a: bool; b: list int; c: list string; d: option (list int) }

let upd (s:bool) (x:r) : ML r =
  if s then { x with a = true } else { x with b = 1 :: x.b; a = not x.a }

let rec go (n:nat) (x:r) : ML r = if n = 0 then x else go (n - 1) (upd (n % 3 = 0) x)

(* The old record is still used after the update: the kept fields are
   counted, and the new values read the old fields. *)
let both (x:r) : ML (r & r) = ({ x with c = "z" :: x.c }, x)

let show (x:r) : ML string =
  string_of_bool x.a ^ " " ^ string_of_int (List.Tot.length x.b) ^ " " ^
  String.concat "," x.c ^ " " ^ (match x.d with Some l -> string_of_int (List.Tot.length l) | None -> "-")

let main () : ML unit =
  let x = go 10 { a = false; b = []; c = ["c"]; d = None } in
  FStar.IO.print_string (show x ^ "\n");
  let y, z = both x in
  FStar.IO.print_string (show y ^ "\n" ^ show z ^ "\n")
