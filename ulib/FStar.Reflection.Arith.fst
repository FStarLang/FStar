module FStar.Reflection.Arith

open FStar.Reflection.Syntax
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

type expr =
    | Lit : int -> expr
    | Plus  : expr -> expr -> expr
    | Mult  : expr -> expr -> expr
    | Neg   : expr -> expr
    // | Div   : expr -> expr -> expr // Add this one?
    | Atom : nat -> expr // uninterpreted atom

type connective =
    | C_Lt | C_Eq | C_Gt | C_Ne

type prop =
    | CompProp : expr -> connective -> expr -> prop
    | AndProp  : prop -> prop -> prop
    | OrProp   : prop -> prop -> prop

let lt e1 e2 = CompProp e1 C_Lt e2
let le e1 e2 = CompProp e1 C_Lt (Plus (Lit 1) e2)
let eq e1 e2 = CompProp e1 C_Eq e2
let ne e1 e2 = CompProp e1 C_Ne e2
let gt e1 e2 = CompProp e1 C_Gt e2
let ge e1 e2 = CompProp (Plus (Lit 1) e1) C_Gt e2

(* Define a traversal monad! Makes exception handling and counter-keeping easy *)
private let tm a = nat -> option (a * nat)
private let return (x:'a) : tm 'a = fun i -> Some (x, i)
private let bind (m : tm 'a) (f : 'a -> tm 'b) : tm 'b =
    fun i -> match m i with
             | Some (x, j) -> f x j
             | None -> None

private let atom : tm nat = fun i -> Some (i, i + 1)
private val fail : (#a:Type) -> tm a
private let fail #a = fun i -> None

let rec forall_list (p:'a -> Type) (l:list 'a) : Type =
    match l with
    | [] -> True
    | x::xs -> p x /\ forall_list p xs

val liftM : ('a -> 'b) -> (tm 'a -> tm 'b)
let liftM f x =
    xx <-- x;
    return (f xx)

val liftM2 : ('a -> 'b -> 'c) -> (tm 'a -> tm 'b -> tm 'c)
let liftM2 f x y =
    xx <-- x;
    yy <-- y;
    return (f xx yy)

let minus x y = Plus x (Neg y)

val is_arith_expr : term -> tm expr
let rec is_arith_expr (t:term) =
    let hd, tl = collect_app t in
    match inspect hd, tl with
    | Tv_FVar fv, [l; r] ->
        let qn = inspect_fv fv in
        collect_app_order t;
        // Have to go through hoops to get F* to typecheck this.
        // Maybe the do notation is twisting the terms somehow unexpected?
        let ll = is_arith_expr (l <: x:term{x << t}) in
        let rr = is_arith_expr (r <: x:term{x << t}) in
        if      eq_qn qn add_qn   then liftM2 Plus ll rr
        else if eq_qn qn minus_qn then liftM2 minus ll rr
        else if eq_qn qn mult_qn  then liftM2 Mult ll rr
        else fail
    | Tv_FVar fv, [a] ->
        let qn = inspect_fv fv in
        collect_app_order t;
        let aa = is_arith_expr (a <: x:term{x << t}) in
        if   eq_qn qn neg_qn then liftM Neg aa
        else fail
    | Tv_Const (C_Int i), _ ->
        return (Lit i)
    | _, _ ->
        fail

val is_arith_prop : term -> tm prop
let rec is_arith_prop (t:term) =
    match term_as_formula t with
    | Eq _ l r -> liftM2 eq (is_arith_expr l) (is_arith_expr r)
    | And l r  -> liftM2 AndProp (is_arith_prop l) (is_arith_prop r)
    | Or l r   -> liftM2  OrProp (is_arith_prop l) (is_arith_prop r)
    | _ -> fail

let test =
    let bind = FStar.Tactics.bind in
    let fail = FStar.Tactics.fail in
    assert_by_tactic (t <-- quote (1 + 2);
                             match is_arith_expr t 0 with
                             | Some (Plus (Lit 1) (Lit 2), _) -> print "alright!"
                             | _ -> fail "oops")
                            True
