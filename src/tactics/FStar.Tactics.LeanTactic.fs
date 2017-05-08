#light "off"
module FStar.Tactics.LeanTactic
open FStar
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util
open FStar.Range
open FStar.TypeChecker.Env

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module SC = FStar.Syntax.Const
module C = FStar.Const
module Env = FStar.TypeChecker.Env
module BU = FStar.Util
module U = FStar.Syntax.Util
module Rel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module N = FStar.TypeChecker.Normalize
open FStar.Tactics.Basic
module E = FStar.Tactics.Embedding
module Core = FStar.Tactics.Basic

type op =
| Add
| Mul
| Conj
| Imp
| Eq
| Heq
| LessThan
| LessThanEq
| GreaterThan
| GreaterThanEq

type lit =
| Number of string

type expr =
| App of expr * list<expr>
| Constant of string
| Pi of list<string * expr> * expr
| Lam of list<string * expr> * expr
| Local of string
| BinOp of op * expr * expr
| Lit of lit

let expr_binder_string (name : string) (ty : string) =
"(" ^ name ^ " : " ^ ty ^ ")"

let bv_to_lean (binder : bv) : string =
binder.ppname.idText ^ "_" ^ string_of_int binder.index

let op_to_string (o : op) : string =
match o with
| Add -> " + "
| Mul -> " * "
| Conj -> " /\\ "
| Imp -> " -> "
| Eq -> " = "
| Heq -> " == "
| LessThan -> " < "
| LessThanEq -> " <= "
| GreaterThan -> " > "
| GreaterThanEq -> " >= "

let lit_to_string (l : lit) : string =
match l with
| Number n -> n

let rec expr_to_string (e : expr) : string =
match e with
| App (f, args) ->
    expr_to_string f ^ " " ^ String.concat " " (List.map expr_to_string args)
| Constant c -> c
| Pi (bs, body) ->
    "forall " ^ String.concat " " (List.map (fun (n, ty) -> expr_binder_string n (expr_to_string ty)) bs)
              ^ ", "
              ^ expr_to_string body
| Lam (bs, body) ->
    "fun " ^ String.concat " " (List.map (fun (n, ty) -> expr_binder_string n (expr_to_string ty)) bs)
           ^ ", "
           ^ expr_to_string body
| Local l -> l
| BinOp (op, e1, e2) ->
    let e1_str = match e1 with
    | BinOp(_, _, _) -> "(" ^ expr_to_string e1 ^ ")"
    | _ -> expr_to_string e1 in
    let e2_str = match e2 with
    | BinOp(_, _, _) -> "(" ^ expr_to_string e2 ^ ")"
    | _ -> expr_to_string e2 in
    e1_str ^ op_to_string op ^ e2_str
| Lit l -> lit_to_string l

let rec tac_seq (xs: list<tac<'a>>) : tac<list<'a>> =
match xs with
| [] -> ret []
| (x :: xs) ->
bind x (fun x' ->
bind (tac_seq xs) (fun xs' ->
    ret (x' :: xs')))

let const_to_lean (c : C.sconst) : tac<expr> =
match c with
| C.Const_effect -> fail "unexpected constant effect"
| C.Const_unit -> fail "unexpected constant unit"
| C.Const_bool _ -> fail "unexpected constant bool"
| C.Const_int (i, _) -> Lit (Number i) |> ret
| C.Const_char _ -> fail "unsupported constant: char"
| C.Const_float _ -> fail "unsupported constant: float"
| C.Const_bytearray _ -> fail "unsupported constant: bytearray"
| C.Const_string  _ -> fail "unsupported constant: string"
| C.Const_range _ -> fail "unsupported constant: range"
| C.Const_reify -> fail "unsupported constant: reify"
| C.Const_reflect _ -> fail "unsupported constant: reflect"

let rec term_to_lean (t : term) : tac<expr> =
match (SS.compress t).n with
| Tm_name n -> ret (Local (bv_to_lean n))
| Tm_fvar v ->
    let str = (Print.fv_to_string v) in
    Local str |> ret
| Tm_app (f, args) ->
    begin match (SS.compress f).n with
    | Tm_uinst (f', us) -> term_app_to_lean f' args
    | _ -> term_app_to_lean f args
    end
| Tm_constant c -> const_to_lean c
| Tm_arrow (bs, c) ->
    let (bs', c') = SS.open_comp bs c in
    bind (convert_binders bs') (fun bs' ->
    Pi (bs', Print.comp_to_string c' |> Constant) |> ret)
| Tm_abs (bs, body, _) ->
    let bs, body' = SS.open_term bs body in
    bind (term_to_lean body') (fun body' ->
    bind (convert_binders bs) (fun bs' ->
    Lam (bs', body') |> ret))
| Tm_delayed _ -> fail ("error found Tm_delayed: " ^ Print.term_to_string t)
| Tm_type  _ -> fail ("error found Tm_type: " ^ Print.term_to_string t)
| Tm_refine _ -> fail ("error found Tm_refine: " ^ Print.term_to_string t)
| Tm_let _ -> fail ("error found Tm_let: " ^ Print.term_to_string t)
| Tm_ascribed _ -> fail ("error found Tm_ascribed: " ^ Print.term_to_string t)
// rely on universe inference for the time being
| Tm_uinst (t, us) -> term_to_lean t
| Tm_bvar i -> fail ("error found Tm_bvar: " ^ Print.term_to_string t)
| _ -> fail ("error: " ^ Print.term_to_string t)
and term_app_to_lean (f : term) (xs : args) =
begin match f.n with
(* This is kind of a hack, talk about how to do this better. *)
| Tm_fvar v when (Print.fv_to_string v) = "b2t" ->
    term_to_lean (List.head (List.map (fun (t, u) -> t) xs))
| Tm_fvar v when (Print.fv_to_string v) = "l_Forall" ->
    let arg_terms = List.map (fun (t', _) -> t') xs in
    let binder_ty = (term_to_lean (List.nth arg_terms 0)) in
    let fn = List.nth arg_terms 1 in
    begin match (SS.compress fn).n with
    | Tm_abs (bs, body, _) ->
        BU.print (Print.term_to_string (SS.compress fn)) [];
        let bs', body' = SS.open_term bs body in
        bind (convert_binders bs') (fun bs' ->
        bind (term_to_lean body') (fun e ->
        Pi (bs', e) |> ret))
    | _ -> fail "internal error: the argument to l_Forall must be an abstraction"
    end
| Tm_fvar v when fv_eq_lid v SC.imp_lid ->
    mk_bin_op 0 Imp xs
// Operators
| Tm_fvar v when fv_eq_lid v SC.eq2_lid ->
   mk_bin_op 1 Eq xs
| Tm_fvar v when fv_eq_lid v SC.op_Addition ->
    mk_bin_op 0 Add xs
| Tm_fvar v when fv_eq_lid v SC.op_LT ->
   mk_bin_op 0 LessThan xs
| Tm_fvar v when fv_eq_lid v SC.op_LTE ->
   mk_bin_op 0 LessThanEq xs
| Tm_fvar v when fv_eq_lid v SC.op_GT ->
   mk_bin_op 0 GreaterThan xs
| Tm_fvar v when fv_eq_lid v SC.op_GTE ->
   mk_bin_op 0 GreaterThanEq xs
| Tm_fvar v when (Print.fv_to_string v) = "op_Star" ->
    mk_bin_op 0 Mul xs
| Tm_fvar v when (Print.fv_to_string v) = "l_and" ->
    mk_bin_op 0 Conj xs
| _ -> bind (term_to_lean f) (fun e ->
       bind (tac_seq (List.map (fun (t, _) -> term_to_lean t) xs)) (fun es ->
       App (e, es) |> ret))
end
and convert_binders (bs : binders) : tac<list<string * expr>> =
match bs with
| [] -> ret []
| ((bv, _) :: bs) ->
    bind (term_to_lean bv.sort) (fun ty ->
    bind (convert_binders bs) (fun bs' ->
        (bv_to_lean bv, ty) :: bs' |> ret))
and mk_bin_op (no_implicits : int) (o : op) (xs : args) : tac<expr> =
    let arg_terms = List.map (fun (t', _) -> t') xs in
        bind (term_to_lean (List.nth arg_terms no_implicits)) (fun e1 ->
        bind (term_to_lean (List.nth arg_terms (no_implicits + 1))) (fun e2 ->
            BinOp (o, e1, e2) |> ret))

let mk_lean_hyps (hyps : list<string * expr>) : string =
String.concat "\n" (List.map (fun (n, t) -> expr_binder_string n (expr_to_string t)) hyps)

let mk_lean_lemma (hyps : list<string * expr>) (goal : expr) (lean_tac : string) : string =
"lemma fstar_goal\n" ^ mk_lean_hyps hyps ^ ": \n" ^ expr_to_string goal ^ " := by " ^ lean_tac ^ "\n"

let lean_tactic_output_dir : ref<bool> = BU.mk_ref false
let lean_goal_counter : ref<int> = BU.mk_ref 0

let fresh_goal_file () =
    let current = !lean_goal_counter in
    let file_name = "goal" ^ string_of_int current ^ ".lean" in
    lean_goal_counter := current + 1;
    file_name

let write_goal (goal_string : string) : unit =
  let outdir = match !lean_tactic_output_dir with
  | false -> BU.mkdir true "lean_tactic_output";
             lean_tactic_output_dir := true
  | true -> () in
  let goal_file = BU.open_file_for_writing ("lean_tactic_output/" ^ fresh_goal_file ()) in
  // We will have to come back and fix this to deal with finding fstar.prims elsewhere.
  let _ = BU.append_to_file goal_file "import ..fstar.prims\nimport smt2\n\nnamespace fstar\n\n" in
  BU.append_to_file goal_file goal_string;
  BU.append_to_file goal_file "\nend fstar"

let lean_tactic : tac<unit> =
bind get (fun ps ->
    let goal_term = ps.main_goal.goal_ty in
    let bs = Env.all_binders ps.main_goal.context in
    bind (term_to_lean goal_term) (fun goal_term ->
    bind (convert_binders bs) (fun hyps ->
        write_goal (mk_lean_lemma hyps goal_term "z3");
        print_proof_state "LEAN:")))
