(** A pretty-printer that allocates all its intermediary strings using the
 * regions library. *)

(* If uncommented, the five lines below replace [Camlstack] with the standard
 * OCaml operations. *)
(* module Camlstack = struct *)
(*   let concat = (^) *)
(*   let push_frame () = () *)
(*   let pop_frame () = () *)
(* end *)

(* -------------------------------------------------------------------------- *)

let (^^) = Camlstack.concat

(* A very simple type of expressions. *)
type expr =
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Const of int

(* A cascade-style pretty-printer that follows the (phantom) parsing rules to
 * insert parentheses exactly where needed (for more information about that
 * style, see http://gallium.inria.fr/blog/a-toy-type-language-1/) *)
let rec print_add = function
  | Add (e1, e2) ->
      print_add e1 ^^ " + " ^^ print_add e2
  | Sub (e1, e2) ->
      print_add e1 ^^ " - " ^^ print_mul e2
  | e ->
      print_mul e

and print_mul = function
  | Mul (e1, e2) ->
      print_mul e1 ^^ " × " ^^ print_mul e2
  | Div (e1, e2) ->
      print_mul e1 ^^ " ÷ " ^^ print_atomic e2
  | e ->
      print_atomic e

and print_atomic = function
  | Const i ->
      string_of_int i
  | e ->
      "(" ^^ print e ^^ ")"

and print e =
  print_add e


(* -------------------------------------------------------------------------- *)

let height = ref 22
let max_runs = ref 30

let arg_spec = [
  "-h", Arg.Set_int height, Printf.sprintf " <NUMBER> set the maximum depth of the expression \
    tree (default: %d)" !height;
  "-n", Arg.Set_int max_runs, Printf.sprintf " <NUMBER> set the maximum number of runs \
    (default: %d)" !max_runs;
]

let arg_usage =
  "USAGE: " ^ Sys.argv.(0) ^ " [OPTIONS]"

let rec gen h =
  if h = 1 then
    Const (Random.int !height)
  else match Random.int 4 with
  | 0 -> Add (gen (h - 1), gen (h - 1))
  | 1 -> Sub (gen (h - 1), gen (h - 1))
  | 2 -> Mul (gen (h - 1), gen (h - 1))
  | 3 -> Div (gen (h - 1), gen (h - 1))
  | _ -> assert false

let _main =
  Arg.parse (Arg.align arg_spec) (fun _ -> ()) arg_usage;
  for __ = 0 to !max_runs do
    Camlstack.push_frame ();
    let e = gen !height in
    ignore (print e);
    Camlstack.pop_frame ();
  done;
  Gc.print_stat stdout
