module FStar.Reflection.Formula

open FStar.Tactics.Effect
open FStar.Tactics.Builtins
open FStar.Reflection.Basic
open FStar.Reflection.Types
open FStar.Reflection.Derived
open FStar.Reflection.Const
open FStar.Reflection.Data

// Cannot open FStar.Tactics.Derived here
let fresh_bv = fresh_bv_named "x"

noeq type comparison =
  | Eq     of option typ  (* Propositional equality (eq2), maybe annotated *)
  | BoolEq of option typ  (* Decidable, boolean equality (eq), maybe annotated *)
  | Lt | Le | Gt | Ge     (* Orderings, at type `int` (and subtypes) *)

noeq type formula =
  | True_  : formula
  | False_ : formula
  | Comp   : comparison -> term -> term -> formula
  | And    : term -> term -> formula
  | Or     : term -> term -> formula
  | Not    : term -> formula
  | Implies: term -> term -> formula
  | Iff    : term -> term -> formula
  | Forall : bv -> term -> formula
  | Exists : bv -> term -> formula
  | App    : term -> term -> formula
  | Name   : bv -> formula
  | FV     : fv -> formula
  | IntLit : int -> formula
  | F_Unknown : formula // Also a baked-in "None"

let mk_Forall (typ : term) (pred : term) : Tac formula =
    let b = pack_bv ({ bv_ppname = "x";
                       bv_sort = typ;
                       bv_index = 0; }) in
    Forall b (pack_ln (Tv_App pred (pack_ln (Tv_BVar b), Q_Explicit)))

let mk_Exists (typ : term) (pred : term) : Tac formula =
    let b = pack_bv ({ bv_ppname = "x";
                       bv_sort = typ;
                       bv_index = 0; }) in
    Exists b (pack_ln (Tv_App pred (pack_ln (Tv_BVar b), Q_Explicit)))

let term_as_formula' (t:term) : Tac formula =
    match inspect_ln t with
    | Tv_Var n ->
        Name n

    | Tv_FVar fv ->
        // Cannot use `when` clauses when verifying!
        let qn = inspect_fv fv in
        if qn = true_qn then True_
        else if qn = false_qn then False_
        else FV fv

    // TODO: l_Forall
    // ...or should we just try to drop all squashes?
    // TODO: b2t at this point ?
    | Tv_App h0 t -> begin
        let (h, ts) = collect_app h0 in
        match inspect_ln h, ts@[t] with
        | Tv_FVar fv, [(a1, Q_Implicit); (a2, Q_Explicit); (a3, Q_Explicit)] ->
            let qn = inspect_fv fv in
            if      qn = eq2_qn then Comp (Eq     (Some a1)) a2 a3
            else if qn = eq1_qn then Comp (BoolEq (Some a1)) a2 a3
            else if qn = lt_qn  then Comp Lt a2 a3
            else if qn = lte_qn then Comp Le a2 a3
            else if qn = gt_qn  then Comp Gt a2 a3
            else if qn = gte_qn then Comp Ge a2 a3
            else App h0 (fst t)
        | Tv_FVar fv, [(a1, Q_Explicit); (a2, Q_Explicit)] ->
            let qn = inspect_fv fv in
            if qn = imp_qn then Implies a1 a2
            else if qn = and_qn then And a1 a2
            else if qn = iff_qn then Iff a1 a2
            else if qn = or_qn  then Or a1 a2
            // Non-annotated comparisons
            else if qn = eq2_qn then Comp (Eq     None) a1 a2
            else if qn = eq1_qn then Comp (BoolEq None) a1 a2
            else App h0 (fst t)

        | Tv_FVar fv, [(a1, Q_Implicit); (a2, Q_Explicit)] ->
            let qn = inspect_fv fv in
                 if qn = forall_qn then mk_Forall a1 a2
            else if qn = exists_qn then mk_Exists a1 a2
            else App h0 (fst t)
        | Tv_FVar fv, [(a, Q_Explicit)] ->
            let qn = inspect_fv fv in
            if qn = not_qn then Not a
            else App h0 (fst t)
        | _ ->
            App h0 (fst t)
        end

    // This case is shady, our logical connectives are squashed and we
    // usually don't get arrows. Nevertheless keeping it in case it helps.
    | Tv_Arrow b c ->
        let bv, _ = inspect_binder b in
        begin match inspect_comp c with
        | C_Total t _ ->
            if is_free bv t
            then Forall bv t
            else Implies (type_of_bv bv) t
        | _ -> F_Unknown
        end

    | Tv_Const (C_Int i) ->
        IntLit i

    // TODO: all these. Do we want to export them?
    | Tv_Type _
    | Tv_Abs _ _
    | Tv_Refine _ _
    | Tv_Const (C_Unit)
    | _ -> 
        F_Unknown

let rec is_name_imp (nm : name) (t : term) : bool =
    begin match inspect_ln t with
    | Tv_FVar fv ->
        if inspect_fv fv = nm
        then true
        else false
    | Tv_App l (_, Q_Implicit) -> // ignore implicits
        is_name_imp nm l
    | _ -> false
    end

let unsquash (t : term) : option term =
    match inspect_ln t with
    | Tv_App l (r, Q_Explicit) ->
        if is_name_imp squash_qn l
        then Some r
        else None
    | _ -> None

let unsquash_total (t : term) : term =
    match inspect_ln t with
    | Tv_App l (r, Q_Explicit) ->
        if is_name_imp squash_qn l
        then r
        else t
    | _ -> t

// Unsquashing
let rec term_as_formula (t:term) : Tac formula =
    match unsquash t with
    | None -> F_Unknown
    | Some t ->
        term_as_formula' t

let rec term_as_formula_total (t:term) : Tac formula =
    term_as_formula' (unsquash_total t)

let formula_as_term_view (f:formula) : Tot term_view =
    let mk_app' tv args = List.Tot.fold_left (fun tv a -> Tv_App (pack_ln tv) a) tv args in
    let e = Q_Explicit in
    let i = Q_Implicit in
    match f with
    | True_  -> Tv_FVar (pack_fv true_qn)
    | False_ -> Tv_FVar (pack_fv false_qn)
    | Comp (Eq None)         l r -> mk_app' (Tv_FVar (pack_fv eq2_qn)) [(l,e);(r,e)]
    | Comp (Eq (Some t))     l r -> mk_app' (Tv_FVar (pack_fv eq2_qn)) [(t,i);(l,e);(r,e)]
    | Comp (BoolEq None)     l r -> mk_app' (Tv_FVar (pack_fv eq1_qn)) [(l,e);(r,e)]
    | Comp (BoolEq (Some t)) l r -> mk_app' (Tv_FVar (pack_fv eq1_qn)) [(t,i);(l,e);(r,e)]
    | Comp Lt l r     -> mk_app' (Tv_FVar (pack_fv lt_qn))  [(l,e);(r,e)]
    | Comp Le l r     -> mk_app' (Tv_FVar (pack_fv lte_qn)) [(l,e);(r,e)]
    | Comp Gt l r     -> mk_app' (Tv_FVar (pack_fv gt_qn))  [(l,e);(r,e)]
    | Comp Ge l r     -> mk_app' (Tv_FVar (pack_fv gte_qn)) [(l,e);(r,e)]
    | And p q         -> mk_app' (Tv_FVar (pack_fv and_qn)) [(p,e);(q,e)]
    | Or  p q         -> mk_app' (Tv_FVar (pack_fv  or_qn)) [(p,e);(q,e)]
    | Implies p q     -> mk_app' (Tv_FVar (pack_fv imp_qn)) [(p,e);(q,e)]
    | Not p           -> mk_app' (Tv_FVar (pack_fv not_qn)) [(p,e)]
    | Iff p q         -> mk_app' (Tv_FVar (pack_fv iff_qn)) [(p,e);(q,e)]
    | Forall b t      -> Tv_Unknown // TODO: decide on meaning of this
    | Exists b t      -> Tv_Unknown // TODO: ^

    | App p q ->
        Tv_App p (q, Q_Explicit)

    | Name b ->
        Tv_Var b

    | FV fv ->
        Tv_FVar fv

    | IntLit i ->
        Tv_Const (C_Int i)

    | F_Unknown ->
        Tv_Unknown

let formula_as_term (f:formula) : Tot term =
    pack_ln (formula_as_term_view f)

let formula_to_string (f:formula) : string =
    match f with
    | True_ -> "True_"
    | False_ -> "False_"
    | Comp (Eq mt) l r -> "Eq" ^
                        (match mt with
                         | None -> ""
                         | Some t -> " (" ^ term_to_string t ^ ")") ^
                        " (" ^ term_to_string l ^ ") (" ^ term_to_string r ^ ")"
    | Comp (BoolEq mt) l r -> "BoolEq" ^
                        (match mt with
                         | None -> ""
                         | Some t -> " (" ^ term_to_string t ^ ")") ^
                        " (" ^ term_to_string l ^ ") (" ^ term_to_string r ^ ")"
    | Comp Lt l r -> "Lt (" ^ term_to_string l ^ ") (" ^ term_to_string r ^ ")"
    | Comp Le l r -> "Le (" ^ term_to_string l ^ ") (" ^ term_to_string r ^ ")"
    | Comp Gt l r -> "Gt (" ^ term_to_string l ^ ") (" ^ term_to_string r ^ ")"
    | Comp Ge l r -> "Ge (" ^ term_to_string l ^ ") (" ^ term_to_string r ^ ")"
    | And p q -> "And (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Or  p q ->  "Or (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Implies p q ->  "Implies (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Not p ->  "Not (" ^ term_to_string p ^ ")"
    | Iff p q ->  "Iff (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Forall bs t -> "Forall <bs> (" ^ term_to_string t ^ ")"
    | Exists bs t -> "Exists <bs> (" ^ term_to_string t ^ ")"
    | App p q ->  "App (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Name bv ->  "Name (" ^ bv_to_string bv ^ ")"
    | FV fv -> "FV (" ^ flatten_name (inspect_fv fv) ^ ")"
    | IntLit i -> "Int " ^ string_of_int i
    | F_Unknown -> "?"
