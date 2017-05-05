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
    | Lt | Eq | Gt | Ne

type prop = | MkProp : expr ->  connective -> expr -> prop

let lt e1 e2 = MkProp e1 Lt e2
let le e1 e2 = MkProp e1 Lt (Plus (Lit 1) e2)
let eq e1 e2 = MkProp e1 Eq e2
let ne e1 e2 = MkProp e1 Ne e2
let gt e1 e2 = MkProp e1 Gt e2
let ge e1 e2 = MkProp (Plus (Lit 1) e1) Gt e2

(* Define a traversal monad! Makes exception handling and counter-keeping easy *)
let tm a = nat -> option (a * nat)
let return (x:'a) : tm 'a = fun i -> Some (x, i)
let bind (m : tm 'a) (f : 'a -> tm 'b) : tm 'b =
    fun i -> match m i with
             | Some (x, j) -> f x j
             | None -> None

let atom : tm nat = fun i -> Some (i, i + 1)
val fail : (#a:Type) -> tm a
let fail #a = fun i -> None

let rec forall_list (p:'a -> Type) (l:list 'a) : Type =
    match l with
    | [] -> True
    | x::xs -> p x /\ forall_list p xs

val decide : term -> tm expr
let rec decide (t:term) =
    let (hd, tl) : term * list term = collect_app t in
    match inspect hd, tl with
    | Tv_FVar fv, [l; r] ->
        let qn = inspect_fv fv in
        collect_app_order t;
        assert(l << t);
        assert(r << t);
        if eq_qn qn add_qn then (l <-- decide l;
                                 r <-- decide r;
                                 return (Plus l r))
        else fail
    | Tv_Const (C_Int i), _ ->
        return (Lit i)
    | _, _ ->
        fail


let test =
    let bind = FStar.Tactics.bind in
    let fail = FStar.Tactics.fail in
    assert_by_tactic (t <-- quote (1 + 2);
                             match decide t 0 with
                             | Some (Plus (Lit 1) (Lit 2), _) -> print "alright!"
                             | _ -> fail "oops")
                            True
