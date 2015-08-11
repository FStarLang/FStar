open AST

exception Error of exn * (int * int * string)

module Lexer = Wlexer
module Parser = Wparser

let print_const (c:const) :string =
  match c with
    | C_prin _
    | C_prins _ -> "some_prin(s)"
    | C_unit -> "()"
    | C_nat n -> string_of_int n
    | C_bool b -> string_of_bool b

let print_pat (p:pat) :string =
  match p with
    | P_const c -> print_const c

let rec print_exp (e:exp) :string =
  match e with
    | Exp (e, _) -> print_exp' e

and print_exp' (e:exp') :string =
  match e with
    | E_aspar (e1, e2) -> "as_par (" ^ print_exp e1 ^ ") (" ^ print_exp e2 ^ ")"
    | E_assec (e1, e2) -> "as_sec (" ^ print_exp e1 ^ ") (" ^ print_exp e2 ^ ")"
    | E_unbox e -> "unbox (" ^ print_exp e ^ ")"
    | E_mkwire (e1, e2) -> "mkwire (" ^ print_exp e1 ^ ") (" ^ print_exp e2 ^ ")"
    | E_projwire (e1, e2) -> "projwire (" ^ print_exp e1 ^ ") (" ^ print_exp e2 ^ ")"
    | E_concatwire (e1, e2) -> "concatwire (" ^ print_exp e1 ^ ") (" ^ print_exp e2 ^ ")"
    | E_const c -> print_const c
    | E_var v -> v
    | E_let (x, e1, e2) -> "let " ^ x ^ " = " ^ print_exp e1 ^ " in\n" ^ print_exp e2
    | E_abs (x, e) -> "fun " ^ x ^ ". " ^ print_exp e
    | E_fix (f, x, e) -> "fix " ^ f ^ ". " ^ x ^ ". " ^ print_exp e
    | E_empabs (x, e) -> "fun " ^ x ^ ". " ^ print_exp e
    | E_app (e1, e2) -> "apply (" ^ print_exp e1 ^ ") (" ^ print_exp e2 ^ ")"
    | E_ffi (s, l) ->
      "ffi " ^ s ^ " [ " ^ (List.fold_left (fun s e -> s ^ print_exp e ^ "; ") "" l) ^ " ]"
    | E_match (e, l) ->
      "match " ^ print_exp e ^ " with\n" ^ (List.fold_left (fun s b -> s ^ print_match_branch b) "" l) ^ "\n"

and print_match_branch ((p, e): pat * exp) :string = "| " ^ (print_pat p) ^ " -> " ^ print_exp e ^ "\n"

let parse_channel :string -> in_channel -> exp =
  fun f i ->
  let lexbuf = Lexing.from_channel i in
  Parser.exp Lexer.token lexbuf

let init_mode =
  let ps = BatSet.union (BatSet.singleton 0) (BatSet.singleton 1) in
  Mode (Par, ps)

let print_terminal (c:config) = match c with
  | Conf (_, _, _, _, t) ->
    match t with
      | T_val (_, v) -> begin
          match v with
            | V_const c -> print_string (print_const c); print_newline ()
            | _ -> print_string "Value print not supported\n"
        end
      | _ -> print_string "Not a terminal configuration"

let _ =
  let f = "SMC.wy" in
  let i = open_in f in
  let e = parse_channel f i in
  print_string ((print_exp e) ^ "\n");
  let init_config = Conf (Source, init_mode, [], empty_env, T_exp e) in
  let c_opt = SourceInterpreter.step_star init_config in
  match c_opt with
    | None -> print_string "Error in interpreter\n"
    | Some c -> print_terminal c
