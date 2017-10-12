module FStar.Reflection.Formula

open FStar.Reflection.Syntax
open FStar.Reflection.Syntax.Lemmas
open FStar.Reflection.Types
open FStar.Reflection.Basic
open FStar.Reflection.Data

type comparison =
  | Eq            (* Propositional equality (eq2) *)
  | BoolEq        (* Decidable, boolean equality (eq) *)
  | Lt | Le       (* Orderings *)

noeq type formula =
  | True_  : formula
  | False_ : formula
  | Comp   : comparison -> typ -> term -> term -> formula
  | And    : term -> term -> formula
  | Or     : term -> term -> formula
  | Not    : term -> formula
  | Implies: term -> term -> formula
  | Iff    : term -> term -> formula
  | Forall : binder -> term -> formula
  | Exists : binder -> term -> formula
  | App    : term -> term -> formula
  | Name   : binder -> formula
  | FV     : fv -> formula
  | IntLit : int -> formula
  | F_Unknown : formula // Also a baked-in "None"

let mk_Forall (typ : term) (pred : term) : formula =
    let b = fresh_binder typ in
    Forall b (pack (Tv_App pred (pack (Tv_Var b), Q_Explicit)))

let mk_Exists (typ : term) (pred : term) : formula =
    let b = fresh_binder typ in
    Exists b (pack (Tv_App pred (pack (Tv_Var b), Q_Explicit)))

val smaller : formula -> term -> Type0
let smaller f t =
    match f with
    | And l r
    | Or l r
    | App l r
    | Implies l r
    | Iff l r ->
        l << t /\ r << t

    | Forall _ p
    | Exists _ p
    | Not p ->
        p << t

    | Comp _ typ l r ->
        typ << t /\ l << t /\ r << t

    | F_Unknown
    | Name _
    | FV _
    | IntLit _
    | True_
    | False_ ->
        True

#reset-options "--z3rlimit 15"
let term_as_formula' (t:term) : Tot (f:formula{smaller f t}) =
    match inspect t with
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
        collect_app_order h0;
        match inspect h, ts@[t] with
        | Tv_FVar fv, [(a1, Q_Implicit); (a2, Q_Explicit); (a3, Q_Explicit)] ->
            let qn = inspect_fv fv in
            if      qn = eq2_qn then Comp Eq a1 a2 a3
            else if qn = eq1_qn then Comp BoolEq a1 a2 a3
            else if qn = lt_qn  then Comp Lt a1 a2 a3
            else if qn = lte_qn then Comp Le a1 a2 a3
            else if qn = gt_qn  then Comp Lt a1 a3 a2
            else if qn = gte_qn then Comp Le a1 a3 a2
            else App h0 (fst t)
        | Tv_FVar fv, [(a1, Q_Explicit); (a2, Q_Explicit)] ->
            let qn = inspect_fv fv in
            if qn = imp_qn then Implies a1 a2
            else if qn = and_qn then And a1 a2
            else if qn = iff_qn then Iff a1 a2
            else if qn = or_qn  then Or a1 a2
            else App h0 (fst t)

        | Tv_FVar fv, [(a1, Q_Implicit); (a2, Q_Explicit)] ->
            let qn = inspect_fv fv in
                 if qn = forall_qn then (admit(); //TODO: admitting termination check for now
                                             mk_Forall a1 a2) //a1 is type, a2 predicate
            else if qn = exists_qn then (admit(); //TODO: admitting termination check for now
                                             mk_Exists a1 a2) //a1 is type, a2 predicate
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
        begin match inspect_comp c with
        | C_Total t ->
            if is_free b t
            then Forall b t
            else Implies (type_of_binder b) t
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
    begin match inspect t with
    | Tv_FVar fv ->
        if inspect_fv fv = nm
        then true
        else false
    | Tv_App l (_, Q_Implicit) -> // ignore implicits
        is_name_imp nm l
    | _ -> false
    end

let unsquash (t : term) : option term =
    match inspect t with
    | Tv_App l (r, Q_Explicit) ->
        if is_name_imp squash_qn l
        then Some r
        else None
    | _ -> None

// Unsquashing
let rec term_as_formula (t:term) : Tot (f:formula{smaller f t}) =
    match unsquash t with
    | None -> F_Unknown
    | Some t ->
        term_as_formula' t

#reset-options

let formula_as_term_view (f:formula) : Tot term_view =
    let mk_app' tv args = List.Tot.fold_left (fun tv a -> Tv_App (pack tv) a) tv args in
    let e = Q_Explicit in
    let i = Q_Implicit in
    match f with
    | True_  -> Tv_FVar (pack_fv true_qn)
    | False_ -> Tv_FVar (pack_fv false_qn)
    | Comp Eq t l r     -> mk_app' (Tv_FVar (pack_fv eq2_qn)) [(t,i);(l,e);(r,e)]
    | Comp BoolEq t l r -> mk_app' (Tv_FVar (pack_fv eq1_qn)) [(t,i);(l,e);(r,e)]
    | Comp Lt t l r     -> mk_app' (Tv_FVar (pack_fv lt_qn))  [(t,i);(l,e);(r,e)]
    | Comp Le t l r     -> mk_app' (Tv_FVar (pack_fv lte_qn)) [(t,i);(l,e);(r,e)]
    | And p q           -> mk_app' (Tv_FVar (pack_fv and_qn)) [(p,e);(q,e)]
    | Or  p q           -> mk_app' (Tv_FVar (pack_fv  or_qn)) [(p,e);(q,e)]
    | Implies p q       -> mk_app' (Tv_FVar (pack_fv imp_qn)) [(p,e);(q,e)]
    | Not p             -> mk_app' (Tv_FVar (pack_fv not_qn)) [(p,e)]
    | Iff p q           -> mk_app' (Tv_FVar (pack_fv iff_qn)) [(p,e);(q,e)]
    | Forall b t        -> Tv_Unknown // TODO: decide on meaning of this
    | Exists b t        -> Tv_Unknown // TODO: ^

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
    pack (formula_as_term_view f)

let formula_to_string (f:formula) : string =
    match f with
    | True_ -> "True_"
    | False_ -> "False_"
    | Comp Eq t l r -> "Eq (" ^ term_to_string t ^ ") (" ^ term_to_string l ^ ") (" ^ term_to_string r ^ ")"
    | Comp BoolEq t l r -> "BoolEq (" ^ term_to_string t ^ ") (" ^ term_to_string l ^ ") (" ^ term_to_string r ^ ")"
    | Comp Lt t l r -> "Lt (" ^ term_to_string t ^ ") (" ^ term_to_string l ^ ") (" ^ term_to_string r ^ ")"
    | Comp Le t l r -> "Le (" ^ term_to_string t ^ ") (" ^ term_to_string l ^ ") (" ^ term_to_string r ^ ")"
    | And p q -> "And (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Or  p q ->  "Or (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Implies p q ->  "Implies (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Not p ->  "Not (" ^ term_to_string p ^ ")"
    | Iff p q ->  "Iff (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Forall bs t -> "Forall <bs> (" ^ term_to_string t ^ ")"
    | Exists bs t -> "Exists <bs> (" ^ term_to_string t ^ ")"
    | App p q ->  "App (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Name b ->  "Name (" ^ inspect_bv b ^ ")"
    | FV fv -> "FV (" ^ flatten_name (inspect_fv fv) ^ ")"
    | IntLit i -> "Int " ^ string_of_int i
    | F_Unknown -> "?"
