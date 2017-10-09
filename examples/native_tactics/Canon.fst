module Canon

open FStar.Tactics
open FStar.Tactics.Arith
module O = FStar.Order
open FStar.Mul

val uncurry : ('a -> 'b -> 'c) -> (tuple2 'a 'b -> 'c)
let uncurry f (x, y) = f x y

val curry : (tuple2 'a 'b -> 'c) -> ('a -> 'b -> 'c)
let curry f x y = f (x, y)

val mk_app_collect_inv_s : (t:term) -> (args:list argv) ->
                            Lemma (uncurry mk_app (collect_app' args t) == mk_app t args)
let rec mk_app_collect_inv_s t args =
    match inspect t with
    | Tv_App l r ->
        mk_app_collect_inv_s l (r::args);
        pack_inspect_inv t
    | _ -> ()

val mk_app_collect_inv : (t:term) -> Lemma (uncurry mk_app (collect_app t) == t)
let rec mk_app_collect_inv t = mk_app_collect_inv_s t []

(*
 * The way back is not stricly true: the list of arguments could grow.
 * It's annoying to even state, might do it later
 *)
let rec forall_list (p:'a -> Type) (l:list 'a) : Type =
    match l with
    | [] -> True
    | x::xs -> p x /\ forall_list p xs

val collect_app_order' : (args:list argv) -> (tt:term) -> (t:term) ->
            Lemma (requires (forall_list (fun a -> a << tt) args)
                             /\ t << tt)
                  (ensures (forall_list (fun a -> a << tt) (snd (collect_app' args t)))
                           /\ fst (collect_app' args t) << tt)
                  (decreases t)
let rec collect_app_order' args tt t =
    match inspect t with
    | Tv_App l r -> collect_app_order' (r::args) tt l
    | _ -> ()

val collect_app_order : (t:term) ->
            Lemma (ensures (forall (f:term). forall (s:list argv). (f,s) == collect_app t ==>
                              (f << t /\ forall_list (fun a -> a << t) (snd (collect_app t)))
                           \/ (f == t /\ s == [])))
let collect_app_order t =
    match inspect t with
    | Tv_App l r -> collect_app_order' [r] t l
    | _ -> ()

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
    | Lit : int -> expr
    | Atom : nat -> term -> expr // atom, contains both a numerical ID and the actual term encountered
    | Plus  : expr -> expr -> expr
    | Mult  : expr -> expr -> expr
    | Minus : expr -> expr -> expr
    | Neg   : expr -> expr
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
private let st = p:(tuple2 nat (list term)){fst p == List.length (snd p)}
private let tm a = st -> either string (tuple2 a st)
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

private let rec find_idx (f : 'a -> bool) (l : list 'a) : option (tuple2 (n:nat{n < List.length l}) 'a) =
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

val is_arith_expr : term -> tm expr
let rec is_arith_expr (t:term) =
    let hd, tl = collect_app t in
    match inspect hd, tl with
    | Tv_FVar fv, [(l, Q_Explicit); (r, Q_Explicit)] ->
        let qn = inspect_fv fv in
        collect_app_order t;
        // Have to go through hoops to get F* to typecheck this.
        // Maybe the do notation is twisting the terms somehow unexpected?
        let ll = is_arith_expr (l <: x:term{x << t}) in
        let rr = is_arith_expr (r <: x:term{x << t}) in
        if      qn = add_qn   then liftM2 Plus ll rr
        else if qn = minus_qn then liftM2 Minus ll rr
        else if qn = mult_qn  then liftM2 Mult ll rr
        else if qn = mult'_qn then liftM2 Mult ll rr
        else fail ("binary: " ^ fv_to_string fv)
    | Tv_FVar fv, [a, Q_Explicit] ->
        let qn = inspect_fv fv in
        collect_app_order t;
        let aa = is_arith_expr (a <: x:term{x << t}) in
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

val distr : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x * (y + z) == x * y + x * z)
let distr #x #y #z = ()

val distl : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) * z == x * z + y * z)
let distl #x #y #z = ()

val ass_plus_l : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x + (y + z) == (x + y) + z)
let ass_plus_l #x #y #z = ()

val ass_mult_l : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x * (y * z) == (x * y) * z)
let ass_mult_l #x #y #z = ()

val comm_plus : (#x : int) -> (#y : int) -> Lemma (x + y == y + x)
let comm_plus #x #y = ()

val sw_plus : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) + z == (x + z) + y)
let sw_plus #x #y #z = ()

val sw_mult : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x * y) * z == (x * z) * y)
let sw_mult #x #y #z = ()

val comm_mult : (#x : int) -> (#y : int) -> Lemma (x * y == y * x)
let comm_mult #x #y = ()

val trans : (#a:Type) -> (#x:a) -> (#z:a) -> (#y:a) ->
                    squash (x == y) -> squash (y == z) -> Lemma (x == z)
let trans #a #x #z #y e1 e2 = ()

val cong_plus : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                squash (w == y) -> squash (x == z) ->
                Lemma (w + x == y + z)
let cong_plus #w #x #y #z p q = ()

val cong_mult : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                squash (w == y) -> squash (x == z) ->
                Lemma (w * x == y * z)
let cong_mult #w #x #y #z p q = ()

val neg_minus_one : (#x:int) -> Lemma (-x == (-1) * x)
let neg_minus_one #x = ()

val mult1 : (#x:int) -> Lemma (x == 1 * x)
let mult1 #x = ()

val x_plus_zero : (#x:int) -> Lemma (x + 0 == x)
let x_plus_zero #x = ()

val zero_plus_x : (#x:int) -> Lemma (0 + x == x)
let zero_plus_x #x = ()

val x_mult_zero : (#x:int) -> Lemma (x * 0 == 0)
let x_mult_zero #x = ()

val zero_mult_x : (#x:int) -> Lemma (0 * x == 0)
let zero_mult_x #x = ()

val x_mult_one : (#x:int) -> Lemma (x * 1 == x)
let x_mult_one #x = ()

val one_mult_x : (#x:int) -> Lemma (1 * x == x)
let one_mult_x #x = ()

val minus_is_plus : (#x : int) -> (#y : int) -> Lemma (x - y == x + (-y))
let minus_is_plus #x #y = ()

open FStar.Tactics

let rec canon_point : unit -> Tac unit = fun () -> (
    let step (t : tactic unit) : tactic unit =
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"trans"]);;
        t
    in
    let step_lemma (lem : tactic term) : tactic unit =
        step (apply_lemma lem)
    in
    let comm_r_plus : tactic unit =
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"sw_plus"]);;
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
        canon_point;;
        trefl
    in
    let comm_r_mult : tactic unit =
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"sw_mult"]);;
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_mult"]);;
        canon_point;;
        trefl
    in
    norm [];;
    g <-- cur_goal;
    let f = term_as_formula g in
    match f with
    | Comp Eq t l r ->
        begin match run_tm (is_arith_expr l) with
        | Inl s ->
            trefl

        // Fold constants
        | Inr (Plus (Lit _) (Lit _))
        | Inr (Mult (Lit _) (Lit _)) ->
            norm [delta; primops];;
            trefl

        // Forget about negations
        | Inr (Neg e) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"neg_minus_one"]);;
            canon_point

        // Distribute
        | Inr (Mult a (Plus b c)) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"distr"]);;
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
            canon_point;;
            canon_point;;
            canon_point

        | Inr (Mult (Plus a b) c) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"distl"]);;
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
            canon_point;;
            canon_point;;
            canon_point

        // Associate to the left
        | Inr (Mult a (Mult b c)) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"ass_mult_l"]);;
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_mult"]);;
            canon_point;;
            canon_point;;
            canon_point

        | Inr (Plus a (Plus b c)) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"ass_plus_l"]);;
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
            canon_point;;
            canon_point;;
            canon_point

        | Inr (Plus (Plus a b) c) ->
            let o = compare_expr b c in
            if O.gt o
            then comm_r_plus
            else trefl

        | Inr (Mult (Mult a b) c) ->
            if O.gt (compare_expr b c)
            then comm_r_mult
            else trefl

        | Inr (Plus a (Lit 0)) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"x_plus_zero"])

        | Inr (Plus (Lit 0) b) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"zero_plus_x"])

        | Inr (Plus a b) ->
            if O.gt (compare_expr a b)
            then apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"comm_plus"])
            else trefl

        | Inr (Mult (Lit 0) _) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"zero_mult_x"])

        | Inr (Mult _ (Lit 0)) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"x_mult_zero"])

        | Inr (Mult (Lit 1) _) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"one_mult_x"])

        | Inr (Mult _ (Lit 1)) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"x_mult_one"])

        | Inr (Mult a b) ->
            if O.gt (compare_expr a b)
            then apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"comm_mult"])
            else trefl

        // Forget about subtraction
        | Inr (Minus a b) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"minus_is_plus"]);;
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
            trefl;;
            canon_point;;
            canon_point

        | Inr _ ->
            trefl
        end
    | _ ->
        fail ("impossible: " ^ term_to_string g)
    ) ()

let canon =
    seq (pointwise canon_point)
        (simpl;; trytac trivial;; idtac)

let compiled_canon (): tactic unit =
    dump "In";;
    canon;;
    dump "Out"
