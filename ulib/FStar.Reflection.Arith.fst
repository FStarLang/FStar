module FStar.Reflection.Arith

open FStar.Reflection.Syntax
open FStar.Reflection.Types
open FStar.Reflection.Syntax.Lemmas
open FStar.Reflection.Basic
open FStar.Reflection.Data
open FStar.Tactics
module O = FStar.Order

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
    // atom, contains both a numerical ID and the actual term encountered
    | Atom    : nat -> term -> expr 
    | Plus    : expr -> expr -> expr
    | Mult    : expr -> expr -> expr
    | Minus   : expr -> expr -> expr
    | Land    : expr -> expr -> expr
    | Lxor    : expr -> expr -> expr
    | Lor     : expr -> expr -> expr
    | Shl     : expr -> expr -> expr
    | Shr     : expr -> expr -> expr
    | Neg     : expr -> expr
    | Udiv    : expr -> expr -> expr
    | Umod    : expr -> expr -> expr
    | MulMod  : expr -> expr -> expr
    | NatToBv : expr -> expr
    // | Div   : expr -> expr -> expr // Add this one?

noeq
type connective =
    | C_Lt | C_Eq | C_Gt | C_Ne

noeq
type prop =
    | CompProp : expr -> connective -> expr -> prop
    | AndProp  : prop -> prop -> prop
    | OrProp   : prop -> prop -> prop
    | NotProp  : prop -> prop

let lt e1 e2 = CompProp e1 C_Lt e2
let le e1 e2 = CompProp e1 C_Lt (Plus (Lit 1) e2)
let eq e1 e2 = CompProp e1 C_Eq e2
let ne e1 e2 = CompProp e1 C_Ne e2
let gt e1 e2 = CompProp e1 C_Gt e2
let ge e1 e2 = CompProp (Plus (Lit 1) e1) C_Gt e2

(* Define a traversal monad! Makes exception handling and counter-keeping easy *)
private let st = p:(nat * list term){fst p == List.length (snd p)}
private let tm a = st -> either string (a * st)
private let return (x:'a) : tm 'a = fun i -> Inr (x, i)
private let bind (m : tm 'a) (f : 'a -> tm 'b) : tm 'b =
    fun i -> match m i with
             | Inl s -> Inl s
             | Inr (x, j) -> f x j

val liftM : ('a -> 'b) -> (tm 'a -> tm 'b)
let liftM f x =
    xx <-- x;
    return (f xx)

val liftM2 : ('a -> 'b -> 'c) -> (tm 'a -> tm 'b -> tm 'c)
let liftM2 f x y =
    xx <-- x;
    yy <-- y;
    return (f xx yy)

val liftM3 : ('a -> 'b -> 'c -> 'd) -> (tm 'a -> tm 'b -> tm 'c -> tm 'd)
let liftM3 f x y z =
    xx <-- x;
    yy <-- y;
    zz <-- z;
    return (f xx yy zz)


private let rec find_idx (f : 'a -> bool) (l : list 'a) : option ((n:nat{n < List.length l}) * 'a) =
    match l with
    | [] -> None
    | x::xs ->
        if f x
        then Some (0, x)
        else begin match find_idx f xs with
             | None -> None
             | Some (i, x) -> Some (i+1, x)
             end

private let atom (t:term) : tm expr = fun (n, atoms) ->
    match find_idx (term_eq t) atoms with
    | None -> Inr (Atom n t, (n + 1, t::atoms))
    | Some (i, t) -> Inr (Atom (n - 1 - i) t, (n, atoms))

private val fail : (#a:Type) -> string -> tm a
private let fail #a s = fun i -> Inl s

let rec forall_list (p:'a -> Type) (l:list 'a) : Type =
    match l with
    | [] -> True
    | x::xs -> p x /\ forall_list p xs

val is_arith_expr : term -> tm expr
let rec is_arith_expr (t:term) =
    let hd, tl = collect_app_ref t in
    // Admitting this subtyping on lists for now, it's provable, but tedious right now
    let tl : list ((a:term{a << t}) * aqualv) = admit(); tl in
    match inspect hd, tl with
    | Tv_FVar fv, [(e1, Q_Implicit); (e2, Q_Explicit) ; (e3, Q_Explicit)] ->
      let qn = inspect_fv fv in
      let e2' = is_arith_expr e2 in
      let e3' = is_arith_expr e3 in
      if qn = land_qn then liftM2 Land e2' e3'
      else if qn = lxor_qn then liftM2 Lxor e2' e3'
      else if qn = lor_qn then liftM2 Lor e2' e3'
      else if qn = shiftr_qn then liftM2 Shr e2' e3'
      else if qn = shiftl_qn then liftM2 Shl e2' e3'
      else if qn = udiv_qn then liftM2 Udiv e2' e3'
      else if qn = umod_qn then liftM2 Umod e2' e3'
      else if qn = mul_mod_qn then liftM2 MulMod e2' e3'
      else fail ("triary: " ^ fv_to_string fv)
    | Tv_FVar fv, [(l, Q_Explicit); (r, Q_Explicit)] ->
        let qn = inspect_fv fv in
        // Have to go through hoops to get F* to typecheck this.
        // Maybe the do notation is twisting the terms somehow unexpected?
        let ll = is_arith_expr l in
        let rr = is_arith_expr r in
        if      qn = add_qn   then liftM2 Plus ll rr
        else if qn = minus_qn then liftM2 Minus ll rr
        else if qn = mult_qn  then liftM2 Mult ll rr
        else if qn = mult'_qn then liftM2 Mult ll rr
        else fail ("binary (ee): " ^ fv_to_string fv)
    | Tv_FVar fv, [(l, Q_Implicit); (r, Q_Explicit)] ->
        let qn = inspect_fv fv in
        let ll = is_arith_expr l in
        let rr = is_arith_expr r in
             if qn = nat_bv_qn then liftM NatToBv rr
        else fail ("binary (ie): " ^ fv_to_string fv)
    | Tv_FVar fv, [(a, Q_Explicit)] ->
        let qn = inspect_fv fv in
        let aa = is_arith_expr a in
        if qn = neg_qn then liftM Neg aa
        else fail ("unary: " ^ fv_to_string fv)
    | Tv_Const (C_Int i), _ ->
        return (Lit i)
    | Tv_FVar _ , []
    | Tv_Var _ , [] ->
        atom t
    | _, _ ->
        fail ("unk (" ^ term_to_string t ^ ")")

val is_arith_prop : term -> tm prop
let rec is_arith_prop (t:term) =
    match term_as_formula t with
    | Comp Eq _ l r     -> liftM2 eq (is_arith_expr l) (is_arith_expr r)
    | Comp BoolEq _ l r -> liftM2 eq (is_arith_expr l) (is_arith_expr r)
    | Comp Lt _ l r     -> liftM2 lt (is_arith_expr l) (is_arith_expr r)
    | Comp Le _ l r     -> liftM2 le (is_arith_expr l) (is_arith_expr r)
    | And l r           -> liftM2 AndProp (is_arith_prop l) (is_arith_prop r)
    | Or l r            -> liftM2  OrProp (is_arith_prop l) (is_arith_prop r)
    | _                 -> fail ("connector (" ^ term_to_string t ^ ")")


// Run the monadic computations, disregard the counter
let run_tm (m : tm 'a) : either string 'a =
    match m (0, []) with
    | Inl s -> Inl s
    | Inr (x, _) -> Inr x

let rec expr_to_string (e:expr) : string =
    match e with
    | Atom i _ -> "a"^(string_of_int i)
    | Lit i -> string_of_int i
    | Plus l r -> "(" ^ (expr_to_string l) ^ " + " ^ (expr_to_string r) ^ ")"
    | Minus l r -> "(" ^ (expr_to_string l) ^ " - " ^ (expr_to_string r) ^ ")"
    | Mult l r -> "(" ^ (expr_to_string l) ^ " * " ^ (expr_to_string r) ^ ")"
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

let rec compare_expr (e1 e2 : expr) : O.order =
    match e1, e2 with
    | Lit i, Lit j -> O.compare_int i j
    | Atom _ t, Atom _ s -> compare_term t s
    | Plus l1 l2, Plus r1 r2
    | Minus l1 l2, Minus r1 r2
    | Mult l1 l2, Mult r1 r2 -> O.lex (compare_expr l1 r1) (fun () -> compare_expr l2 r2)
    | Neg e1, Neg e2 -> compare_expr e1 e2
    | Lit _,    _ -> O.Lt    | _, Lit _    -> O.Gt
    | Atom _ _, _ -> O.Lt    | _, Atom _ _ -> O.Gt
    | Plus _ _, _ -> O.Lt    | _, Plus _ _ -> O.Gt
    | Mult _ _, _ -> O.Lt    | _, Mult _ _ -> O.Gt
    | Neg _,    _ -> O.Lt    | _, Neg _    -> O.Gt
    | _ -> O.Gt // don't care about this for now
