module FStar.Reflection.Arith

open FStar.Reflection.Syntax

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
    | Sum   : expr -> expr -> expr
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
let bind (m : tm 'a) (f : 'a -> tm 'b) : tm 'b = fun i -> match m i with
                                                          | Some (x, j) -> f x j
                                                          | None -> None
let atom : tm nat = fun i -> Some (i, i + 1)
let fail : tm 'a = fun i -> None

val decide : term -> tm expr
let rec decide t =
    let hd, tl = collect_app t in
    match inspect hd, tl with
    | Tm_fvar fv, [l; r] ->
        let qn = inspectfv fv in
        if eq_qn qn add_qn then (l <-- decide l;
                                 r <-- decide r;
                                 return (Sum l r))
        else fail
    | _ -> fail
