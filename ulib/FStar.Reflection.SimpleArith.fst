module FStar.Reflection.SimpleArith

open FStar.Reflection.Syntax
open FStar.Reflection.Types
open FStar.Reflection.Syntax.Lemmas
open FStar.Reflection.Basic
open FStar.Reflection.Data
open FStar.Tactics

(*
 * Simple decision procedure to decide if a term is an "arithmetic
 * proposition", by which we mean a simple relation between two
 * arithmetic expressions (each representing integers or naturals)
 *
 * Main use case: deciding, in a tactic, if a goal is an arithmetic
 * expression and applying a custom decision procedure there (instead of
 * feeding to the SMT solver)
 *)

noeq
type expr =
    | Lit     : int -> expr
    //atom, contains both a numerical ID and the actual term encountered
    | Atom    : term -> expr 
    | Land    : expr -> expr -> expr
    | Lxor    : expr -> expr -> expr
    | Lor     : expr -> expr -> expr
    | Ladd    : expr -> expr -> expr
    | Shl     : expr -> expr -> expr
    | Shr     : expr -> expr -> expr
    | Neg     : expr -> expr
    | Udiv    : expr -> expr -> expr
    | Umod    : expr -> expr -> expr
    | MulMod  : expr -> expr -> expr
    | NatToBv : expr -> expr
    | MkUInt32  : expr -> expr
    | Unknown : expr
    // | Div   : expr -> expr -> expr // Add this one?

let rec forall_list (p:'a -> Type) (l:list 'a) : Type =
    match l with
    | [] -> True
    | x::xs -> p x /\ forall_list p xs

val is_arith_expr : term -> expr
let rec is_arith_expr (t:term) =
    let hd, tl = collect_app_ref t in
    // Admitting this subtyping on lists for now, it's provable, but tedious right now
    let tl : list ((a:term{a << t}) * aqualv) = admit(); tl in
    match inspect hd, tl with
    | Tv_FVar fv, [(e1, _); (e2, _) ; (e3, _)] ->
      let qn = inspect_fv fv in
      let e2' = is_arith_expr e2 in
      let e3' = is_arith_expr e3 in
      if qn = land_qn then Land e2' e3'
      else if qn = lxor_qn then Lxor e2' e3'
      else if qn = lor_qn then Lor e2' e3'
      else if qn = shiftr_qn then Shr e2' e3'
      else if qn = shiftl_qn then Shl e2' e3'
      else if qn = udiv_qn then Udiv e2' e3'
      else if qn = umod_qn then Umod e2' e3'
      else if qn = mul_mod_qn then MulMod e2' e3'
      else if qn = ladd_qn then Ladd e2' e3'
      else Unknown
    | Tv_FVar fv, [(l, Q_Implicit); (r, _)] ->
        let qn = inspect_fv fv in
        let ll = is_arith_expr l in //TODO:REMOVE
        let rr = is_arith_expr r in
        if qn = nat_bv_qn then NatToBv rr
        else Unknown
    | Tv_FVar fv, [(a, Q_Explicit)] ->
        let qn = inspect_fv fv in
        let aa = is_arith_expr a in
        if qn = neg_qn then Neg aa
	else if qn = mk32_qn then MkUInt32 aa
        else Unknown
    | Tv_Const (C_Int i), _ ->
        Lit i
    | Tv_FVar _ , []
    | Tv_Var _ , [] ->
        Atom t
    | _, _ ->
        Unknown

let rec expr_to_string (e:expr) : string =
    match e with
    | Atom _ -> "a"
    | Lit i -> string_of_int i
    | Neg l -> "(- " ^ (expr_to_string l) ^ ")"
    | Land l r -> "(" ^ (expr_to_string l) ^ " & " ^ (expr_to_string r) ^ ")"
    | Lor l r -> "(" ^ (expr_to_string l) ^ " | " ^ (expr_to_string r) ^ ")"
    | Lxor l r -> "(" ^ (expr_to_string l) ^ " ^ " ^ (expr_to_string r) ^ ")"
    | Shl l r -> "(" ^ (expr_to_string l) ^ " << " ^ (expr_to_string r) ^ ")"
    | Shr l r -> "(" ^ (expr_to_string l) ^ " >> " ^ (expr_to_string r) ^ ")"
    | NatToBv l -> "(" ^ "to_vec " ^ (expr_to_string l) ^ ")"
    | Neg l -> "~ " ^ (expr_to_string l)
    | Udiv l r -> "(" ^ (expr_to_string l) ^ " / " ^ (expr_to_string r) ^ ")"
    | Umod l r -> "(" ^ (expr_to_string l) ^ " % " ^ (expr_to_string r) ^ ")"
    | MulMod l r -> "(" ^ (expr_to_string l) ^ " ** " ^ (expr_to_string r) ^ ")"
    | MkUInt32 l -> "Mk " ^ (expr_to_string l)
    | Unknown -> "Unknown"
