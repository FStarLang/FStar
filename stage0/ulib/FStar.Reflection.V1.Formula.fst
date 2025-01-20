(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Reflection.V1.Formula

open FStar.List.Tot.Base
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V1.Builtins
open FStar.Stubs.Reflection.Types
open FStar.Reflection.Const
open FStar.Stubs.Reflection.V1.Builtins
open FStar.Reflection.V1.Derived
open FStar.Stubs.Reflection.V1.Data

///// Cannot open FStar.Tactics.Derived here /////
private let bv_to_string (bv : bv) : Tac string =
    let bvv = inspect_bv bv in
    unseal (bvv.bv_ppname)
private let rec inspect_unascribe (t:term) : Tac (tv:term_view{notAscription tv}) =
  match inspect t with
  | Tv_AscribedT t _ _ _
  | Tv_AscribedC t _ _ _ ->
    inspect_unascribe t
  | tv -> tv
private let rec collect_app' (args : list argv) (t : term)
  : Tac (term & list argv) =
    match inspect_unascribe t with
    | Tv_App l r ->
        collect_app' (r::args) l
    | _ -> (t, args)
private let collect_app = collect_app' []
/////

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
  | Forall : bv -> typ -> term -> formula
  | Exists : bv -> typ -> term -> formula
  | App    : term -> term -> formula
  | Name   : bv -> formula
  | FV     : fv -> formula
  | IntLit : int -> formula
  | F_Unknown : formula // Also a baked-in "None"

let mk_Forall (typ : term) (pred : term) : Tac formula =
    let b = pack_bv ({ bv_ppname = as_ppname "x";
                       bv_index = 0; }) in
    Forall b typ (pack_ln (Tv_App pred (pack_ln (Tv_BVar b), Q_Explicit)))

let mk_Exists (typ : term) (pred : term) : Tac formula =
    let b = pack_bv ({ bv_ppname = as_ppname "x";
                       bv_index = 0; }) in
    Exists b typ (pack_ln (Tv_App pred (pack_ln (Tv_BVar b), Q_Explicit)))

let term_as_formula' (t:term) : Tac formula =
    match inspect_unascribe t with
    | Tv_Var n ->
        Name n

    | Tv_FVar fv
    | Tv_UInst fv _ ->
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
        let h = un_uinst h in
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
            else if qn = b2t_qn then begin
              if term_eq a (`false) then False_
              else if term_eq a (`true) then True_
              else App h0 (fst t)
            end
            else App h0 (fst t)
        | _ ->
            App h0 (fst t)
        end

    | Tv_Const (C_Int i) ->
        IntLit i

    (* Not formulas. *)
    | Tv_Let _ _ _ _ _ _
    | Tv_Match _ _ _
    | Tv_Type _
    | Tv_Abs _ _
    | Tv_Arrow _ _
    | Tv_Uvar _ _
    | Tv_Unknown
    | Tv_Unsupp
    | Tv_Refine _ _ _ -> F_Unknown

    (* Other constants? *)
    | Tv_Const _ -> F_Unknown

    (* Should not occur, we're using inspect_ln *)
    | Tv_BVar _ -> F_Unknown

// Unsquashing
let term_as_formula (t:term) : Tac formula =
    match unsquash_term t with
    | None -> F_Unknown
    | Some t ->
        term_as_formula' t

let term_as_formula_total (t:term) : Tac formula =
    term_as_formula' (maybe_unsquash_term t)

let formula_as_term_view (f:formula) : Tot term_view =
    let mk_app' tv args = List.Tot.Base.fold_left (fun tv a -> Tv_App (pack_ln tv) a) tv args in
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
    | Forall b sort t -> Tv_Unknown // TODO: decide on meaning of this
    | Exists b sort t -> Tv_Unknown // TODO: ^

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

let formula_to_string (f:formula) : Tac string =
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
    | Forall bs _sort t -> "Forall <bs> (" ^ term_to_string t ^ ")"
    | Exists bs _sort t -> "Exists <bs> (" ^ term_to_string t ^ ")"
    | App p q ->  "App (" ^ term_to_string p ^ ") (" ^ term_to_string q ^ ")"
    | Name bv ->  "Name (" ^ bv_to_string bv ^ ")"
    | FV fv -> "FV (" ^ flatten_name (inspect_fv fv) ^ ")"
    | IntLit i -> "Int " ^ string_of_int i
    | F_Unknown -> "?"
