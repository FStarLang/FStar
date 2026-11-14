module CherryTupleMatch

(* A match on a tuple of variables does not count the tuple: what the
   patterns bind is borrowed from the components, which stay alive for as
   long as it is used. *)

open FStar.All

type step = | A | B | Ex of step | L of list string

let rec eq_step (s1 s2:step) : ML bool =
  match s1, s2 with
  | A, A | B, B -> true
  | Ex a, Ex b -> eq_step a b
  | L x, L y -> x = y
  | _, _ -> false

let pick (s1 s2:step) : ML step =
  match s1, s2 with
  | Ex a, _ -> a
  | _, Ex b -> b
  | _ -> s1

(* The components are owned (they are stored), and what is bound from them
   outlives the moves. *)
let keep (s1 s2:step) : ML (list step) =
  match s1, s2 with
  | Ex a, _ -> [s1; a; s2]
  | t, L xs -> [Ex s2; t; L xs; s1]
  | _ -> [s1]

let three (n:int) (s1 s2:step) : ML string =
  match n, s1, s2 with
  | 0, Ex (L (x :: _)), _ | 1, _, Ex (L (x :: _)) -> x
  | _, L xs, L ys -> String.concat "," (FStar.List.Tot.append xs ys)
  | _ -> "none"

let rec show (s:step) : ML string =
  match s with
  | A -> "A" | B -> "B"
  | Ex s -> "Ex(" ^ show s ^ ")"
  | L xs -> "[" ^ String.concat ";" xs ^ "]"

let main () : ML unit =
  let x = Ex (Ex (L ["a"; "b"])) in
  let y = Ex (Ex (L ["a"; "b"])) in
  FStar.IO.print_string (string_of_bool (eq_step x y) ^ "\n");
  FStar.IO.print_string (string_of_bool (eq_step x (Ex A)) ^ "\n");
  FStar.IO.print_string (show (pick (Ex (L ["c"])) y) ^ "\n");
  FStar.IO.print_string (show (pick A y) ^ "\n");
  FStar.IO.print_string (show (pick A B) ^ "\n");
  FStar.IO.print_string (String.concat " " (List.map show (keep (Ex (L ["d"])) B)) ^ "\n");
  FStar.IO.print_string (String.concat " " (List.map show (keep (L ["e"]) (L ["f"; "g"]))) ^ "\n");
  FStar.IO.print_string (String.concat " " (List.map show (keep A B)) ^ "\n");
  FStar.IO.print_string (three 0 (Ex (L ["h"])) A ^ " " ^ three 1 A (Ex (L ["i"])) ^ " " ^
                         three 2 (L ["j"]) (L ["k"]) ^ " " ^ three 3 A A ^ "\n")
