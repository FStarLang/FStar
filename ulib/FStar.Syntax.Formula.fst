module FStar.Syntax.Formula

open FStar.Syntax.Base

noeq type formula =
  | True_  : formula
  | False_ : formula
  | Eq     : typ -> term -> term -> formula
  | And    : term -> term -> formula
  | Or     : term -> term -> formula
  | Not    : term -> formula
  | Implies: term -> term -> formula
  | Iff    : term -> term -> formula
  | Forall : binders -> term -> formula
  | Exists : binders -> term -> formula
  | App    : term -> term -> formula
  | Name   : binder -> formula
  | FV     : fv -> formula
  | IntLit : int -> formula
  | F_Unknown : formula // Also a baked-in "None"

// TODO: move away
let rec eqlist (f : 'a -> 'a -> bool) (xs : list 'a) (ys : list 'a) : Tot bool =
    match xs, ys with
    | [], [] -> true
    | x::xs, y::ys -> f x y && eqlist f xs ys
    | _ -> false

let eq_qn = eqlist (fun s1 s2 -> String.compare s1 s2 = 0) 

let rec collect_app' (args : list term) (t : term) : Tot (term * list term) (decreases t) =
    match inspect t with
    | Tv_App l r ->
        assume(l << t);
        collect_app' (r::args) l
    | _ -> (t, args)
let collect_app = collect_app' []

let rec mk_app (t : term) (args : list term) : Tot term (decreases args) =
    match args with
    | [] -> t
    | (x::xs) -> mk_app (pack (Tv_App t x)) xs

(* We could prove the previous two functions are inverses given some specs about pack/inspect *)

let term_as_formula (t:term) : formula =
    match inspect t with
    | Tv_Var n ->
        Name n

    | Tv_FVar qn ->
        FV qn

    | Tv_App h0 t -> begin
        let (h, ts) = collect_app' [t] h0 in
        // Cannot use `when` clauses when verifying!
        match inspect h, ts with
        | Tv_FVar fv, [a1; a2] ->
            let qn = inspect_fv fv in
            if eq_qn qn imp_qn then Implies a1 a2
            else if eq_qn qn and_qn then And a1 a2
            else if eq_qn qn or_qn  then Or a1 a2
            else F_Unknown
        | Tv_FVar fv, [a] ->
            let qn = inspect_fv fv in
            if eq_qn qn not_qn then Not a
            else F_Unknown
        | _ ->
            App h0 t
        end

    | Tv_Arrow b t ->
        // TODO: collect binders?
        // TODO: if not free, it's an implication?
        Forall [b] t
    | Tv_Const (C_Int i) ->
        IntLit i

    // TODO: all these
    | Tv_Type ()
    | Tv_Abs _ _
    | Tv_Refine _ _
    | Tv_Const (C_Unit)
    | _ -> 
        F_Unknown

// TODO: formula as term
