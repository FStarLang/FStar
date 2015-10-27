(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"

module FStar.ToSMT.Term

open System.Diagnostics
open FStar
open FStar.Absyn.Syntax
open FStar.Absyn
open FStar.Util

type sort =
  | Bool_sort
  | Int_sort
  | Kind_sort
  | Type_sort
  | Term_sort
  | String_sort
  | Ref_sort
  | Fuel_sort
  | Array of sort * sort
  | Arrow of sort * sort
  | Sort of string

let rec strSort x = match x with
  | Bool_sort  -> "Bool"
  | Int_sort  -> "Int"
  | Kind_sort -> "Kind"
  | Type_sort -> "Type"
  | Term_sort -> "Term"
  | String_sort -> "String"
  | Ref_sort -> "Ref"
  | Fuel_sort -> "Fuel"
  | Array(s1, s2) -> format2 "(Array %s %s)" (strSort s1) (strSort s2)
  | Arrow(s1, s2) -> format2 "(%s -> %s)" (strSort s1) (strSort s2)
  | Sort s -> s

type op =
  | True
  | False
  | Not
  | And
  | Or
  | Imp
  | Iff
  | Eq
  | LT
  | LTE
  | GT
  | GTE
  | Add
  | Sub
  | Div
  | Mul
  | Minus
  | Mod
  | ITE
  | Var of string //Op corresponding to a user/encoding-defined uninterpreted function

type qop =
  | Forall
  | Exists

//de Bruijn representation of terms in locally nameless style
type term' =
  | Integer    of string //unbounded mathematical integers
  | BoundV     of int
  | FreeV      of fv
  | App        of op  * list<term> //ops are always fully applied; we're in a first-order theory
  | Quant      of qop
                  * list<list<pat>>  //disjunction of conjunctive patterns
                  * option<int>      //an optional weight; seldom used
                  * list<sort>       //sorts of each bound variable
                  * term             //body
and pat  = term
and term = {tm:term'; hash:string; freevars:Syntax.memo<fvs>}
and fv = string * sort
and fvs = list<fv>

let fv_eq (x:fv) (y:fv) = fst x = fst y
let fv_sort x = snd x
let freevar_eq x y = match x.tm, y.tm with
    | FreeV x, FreeV y -> fv_eq x y
    | _ -> false
let freevar_sort  = function
    | {tm=FreeV x} -> fv_sort x
    | _ -> failwith "impossible"
let fv_of_term = function
    | {tm=FreeV fv} -> fv
    | _ -> failwith "impossible"
let rec freevars t = match t.tm with
  | Integer _
  | BoundV _ -> []
  | FreeV fv -> [fv]
  | App(_, tms) -> List.collect freevars tms
  | Quant(_, _, _, _, t) -> freevars t

//memo-ized
let free_variables t = match !t.freevars with
  | Some b -> b
  | None ->
    let fvs = Util.remove_dups fv_eq (freevars t) in
    t.freevars := Some fvs;
    fvs

(*****************************************************)
(* Pretty printing terms and decls in SMT Lib format *)
(*****************************************************)
let qop_to_string = function
  | Forall -> "forall"
  | Exists -> "exists"

let op_to_string = function
  | True -> "true"
  | False -> "false"
  | Not -> "not"
  | And -> "and"
  | Or  -> "or"
  | Imp -> "implies"
  | Iff -> "iff"
  | Eq  -> "="
  | LT  -> "<"
  | LTE -> "<="
  | GT  -> ">"
  | GTE -> ">="
  | Add -> "+"
  | Sub -> "-"
  | Div -> "div"
  | Mul -> "*"
  | Minus -> "-"
  | Mod  -> "mod"
  | ITE -> "ite"
  | Var s -> s

let weightToSmt = function
    | None -> ""
    | Some i -> Util.format1 ":weight %s\n" (string_of_int i)

let rec hash_of_term' t = match t with
    | Integer i ->  i
    | BoundV i  -> "@"^string_of_int i
    | FreeV x   -> fst x ^ ":" ^ strSort (snd x) //Question: Why is the sort part of the hash?
    | App(op, tms) -> "("^(op_to_string op)^(List.map (fun t -> t.hash) tms |> String.concat " ")^")"
    | Quant(qop, pats, wopt, sorts, body) ->
        Util.format5 "(%s (%s)(! %s %s %s))"
            (qop_to_string qop)
            (List.map strSort sorts |> String.concat " ")
            body.hash
            (weightToSmt wopt)
            (pats |> List.map (fun pats -> (List.map (fun p -> p.hash) pats |> String.concat " ")) |> String.concat "; ")

//The hash-cons table
let __all_terms = ref (Util.smap_create<term> 10000)
let all_terms () = !__all_terms
let mk t =
    let key = hash_of_term' t in
    match Util.smap_try_find (all_terms()) key with
        | Some tm -> tm
        | None ->
          let tm = {tm=t; hash=key; freevars=Util.mk_ref None} in
          Util.smap_add (all_terms()) key tm;
          tm

let mkTrue       = mk (App(True, []))
let mkFalse      = mk (App(False, []))
let mkInteger i  = mk (Integer i)
let mkInteger32 i = mkInteger (string_of_int32 i)
let mkInteger' i  = mkInteger (string_of_int i)
let mkBoundV i   = mk (BoundV i)
let mkFreeV x    = mk (FreeV x)
let mkApp' f        = mk (App f)
let mkApp (s, args) = mk (App (Var s, args))
let mkNot t      = match t.tm with
    | App(True, _)  -> mkFalse
    | App(False, _) -> mkTrue
    | _ -> mkApp'(Not, [t])
let mkAnd (t1, t2)  = match t1.tm, t2.tm with
    | App(True, _), _ -> t2
    | _, App(True, _) -> t1
    | App(False, _), _
    | _, App(False, _) -> mkFalse
    | App(And, ts1), App(And, ts2) -> mkApp'(And, ts1@ts2)
    | _, App(And, ts2) -> mkApp'(And, t1::ts2)
    | App(And, ts1), _ -> mkApp'(And, ts1@[t2])
    | _ -> mkApp'(And, [t1;t2])
let mkOr (t1, t2)  = match t1.tm, t2.tm with
    | App(True, _), _
    | _, App(True, _) -> mkTrue
    | App(False, _), _ -> t2
    | _, App(False, _) -> t1
    | App(Or, ts1), App(Or, ts2) -> mkApp'(Or, ts1@ts2)
    | _, App(Or, ts2) -> mkApp'(Or, t1::ts2)
    | App(Or, ts1), _ -> mkApp'(Or, ts1@[t2])
    | _ -> mkApp'(Or, [t1;t2])
let mkImp (t1, t2) = match t1.tm, t2.tm with
    | _, App(True, _) -> mkTrue
    | App(True, _), _ -> t2
    | _, App(Imp, [t1'; t2']) -> mkApp'(Imp, [mkAnd(t1, t1'); t2'])
    | _ -> mkApp'(Imp, [t1; t2])

let mk_bin_op op (t1,t2) = mkApp'(op, [t1;t2])
let mkMinus t = mkApp'(Minus, [t])
let mkIff = mk_bin_op Iff
let mkEq  = mk_bin_op Eq
let mkLT  = mk_bin_op LT
let mkLTE = mk_bin_op LTE
let mkGT  = mk_bin_op GT
let mkGTE = mk_bin_op GTE
let mkAdd = mk_bin_op Add
let mkSub = mk_bin_op Sub
let mkDiv = mk_bin_op Div
let mkMul = mk_bin_op Mul
let mkMod = mk_bin_op Mod
let mkITE (t1, t2, t3) =
    match t2.tm, t3.tm with
        | App(True,_), App(True, _) -> mkTrue
        | App(True,_), _ -> mkImp (mkNot t1, t3)
        | _, App(True, _) -> mkImp(t1, t2)
        | _, _ ->  mkApp'(ITE, [t1; t2; t3])
let mkCases t = match t with
    | [] -> failwith "Impos"
    | hd::tl -> List.fold_left (fun out t -> mkAnd (out, t)) hd tl

let mkQuant (qop, pats, wopt, vars, body) =
    if List.length vars = 0 then body
    else match body.tm with
            | App(True, _) -> body
            | _ -> mk (Quant(qop,pats,wopt,vars,body))

(*****************************************************)
(* abstracting free names; instantiating bound vars  *)
(*****************************************************)
let abstr fvs t = //fvs is a subset of the free vars of t; the result closes over fvs
    let nvars = List.length fvs in
    let index_of fv = match Util.try_find_index (fv_eq fv) fvs with
        | None -> None
        | Some i -> Some (nvars - (i + 1)) in
    let rec aux ix t =
        match !t.freevars with
            | Some [] -> t
            | _ ->
            begin match t.tm with
                | Integer _
                | BoundV _ -> t
                | FreeV x ->
                  begin match index_of x with
                    | None -> t
                    | Some i -> mkBoundV (i + ix)
                  end
                | App(op, tms) -> mkApp'(op, List.map (aux ix) tms)
                | Quant(qop, pats, wopt, vars, body) ->
                  let n = List.length vars in
                  mkQuant(qop, pats |> List.map (List.map (aux (ix + n))), wopt, vars, aux (ix + n) body)
           end in
    aux 0 t

let inst tms t =
    let n = List.length tms in //instantiate the first n BoundV's with tms, in order
    let rec aux shift t = match t.tm with
        | Integer _
        | FreeV _ -> t
        | BoundV i ->
          if 0 <= i - shift && i - shift < n
          then List.nth tms (i - shift)
          else t
        | App(op, tms) -> mkApp'(op, List.map (aux shift) tms)
        | Quant(qop, pats, wopt, vars, body) ->
          let m = List.length vars in
          let shift = shift + m in
          mkQuant(qop, pats |> List.map (List.map (aux shift)), wopt, vars, aux shift body) in
   aux 0 t

let mkQuant' (qop, pats, wopt, vars, body) = mkQuant (qop, pats |> List.map (List.map (abstr vars)), wopt, List.map fv_sort vars, abstr vars body)
let mkForall'' (pats, wopt, sorts, body) = mkQuant (Forall, pats, wopt, sorts, body)
let mkForall' (pats, wopt, vars, body) = mkQuant' (Forall, pats, wopt, vars, body)

//these are the external facing functions for building quantifiers
let mkForall (pats, vars, body) = mkQuant' (Forall, pats, None, vars, body)
let mkExists (pats, vars, body) = mkQuant' (Exists, pats, None, vars, body)


type caption = option<string>
type binders = list<(string * sort)>
type projector = (string * sort)
type constructor_t = (string * list<projector> * sort * int)
type constructors  = list<constructor_t>
type decl =
  | DefPrelude
  | DeclFun    of string * list<sort> * sort * caption        //uninterpreted function
  | DefineFun  of string * list<sort> * sort * term * caption //defined function
  | Assume     of term   * caption
  | Caption    of string
  | Eval       of term
  | Echo       of string
  | Push
  | Pop
  | CheckSat
type decls_t = list<decl>

let mkDefineFun (nm, vars, s, tm, c) = DefineFun(nm, List.map fv_sort vars, s, abstr vars tm, c)
let constr_id_of_sort sort = format1 "%s_constr_id" (strSort sort)
let fresh_token (tok_name, sort) id =
    Assume(mkEq(mkInteger' id, mkApp(constr_id_of_sort sort, [mkApp (tok_name,[])])), Some "fresh token")

let constructor_to_decl (name, projectors, sort, id) =
    let id = string_of_int id in
    let cdecl = DeclFun(name, projectors |> List.map snd, sort, Some "Constructor") in
    let n_bvars = List.length projectors in
    let bvar_name i = "x_" ^ string_of_int i in
    let bvar_index i = n_bvars - (i + 1) in
    let bvar i s = mkFreeV(bvar_name i, s) in
    let bvars = projectors |> List.mapi (fun i (_, s) -> bvar i s) in
    let bvar_names = List.map fv_of_term bvars in
    let capp = mkApp(name, bvars) in
    let cid_app = mkApp(constr_id_of_sort sort, [capp]) in
    let cid = Assume(mkForall([[capp]], bvar_names, mkEq(mkInteger id, cid_app)), Some "Constructor distinct") in //specifically omitting pattern
    let disc_name = "is-"^name in
    let xfv = ("x", sort) in
    let xx = mkFreeV xfv in
    let disc_eq = mkEq(mkApp(constr_id_of_sort sort, [xx]), mkInteger id) in
    let proj_terms = projectors |> List.map (fun (proj, s) -> mkApp(proj, [xx])) in
    let disc_inv_body = mkEq(xx, mkApp(name, proj_terms)) in
    let disc_ax = mkAnd(disc_eq, disc_inv_body)  in
    let disc = mkDefineFun(disc_name, [xfv], Bool_sort,
                           disc_ax,
                           Some "Discriminator definition") in
    let projs = projectors |> List.mapi (fun i (name, s) ->
        let cproj_app = mkApp(name, [capp]) in
        [DeclFun(name, [sort], s, Some "Projector");
         Assume(mkForall([[capp]], bvar_names, mkEq(cproj_app, bvar i s)), Some "Projection inverse")]) |> List.flatten in
    Caption (format1 "<start constructor %s>" name)::cdecl::cid::projs@[disc]@[Caption (format1 "</end constructor %s>" name)]


(****************************************************************************)
(* Standard SMTLib prelude for F* and some term constructors                *)
(****************************************************************************)
let name_binders_inner outer_names start sorts =
    let names, binders, n = sorts |> List.fold_left (fun (names, binders, n) s ->
        let prefix = match s with
            | Type_sort -> "@a"
            | Term_sort -> "@x"
            | _ -> "@u" in
        let nm = prefix ^ string_of_int n in
        let names = (nm,s)::names in
        let b = Util.format2 "(%s %s)" nm (strSort s) in
        names, b::binders, n+1)
        (outer_names, [], start)  in
    names, List.rev binders, n

let name_binders sorts =
    let names, binders, n = name_binders_inner [] 0 sorts in
    List.rev names, binders

let termToSmt t =
    let rec aux n (names:list<fv>) t = match t.tm with
      | Integer i     -> i
      | BoundV i ->
        List.nth names i |> fst
      | FreeV x -> fst x
      | App(op, []) -> op_to_string op
      | App(op, tms) -> Util.format2 "(%s %s)" (op_to_string op) (List.map (aux n names) tms |> String.concat "\n")
      | Quant(qop, pats, wopt, sorts, body) ->
        let names, binders, n = name_binders_inner names n sorts in
        let binders = binders |> String.concat " " in
        let pats_str = match pats with
            | [[]]
            | [] -> ""
            | _ -> pats |> List.map (fun pats -> format1 "\n:pattern (%s)" (String.concat " " (List.map (fun p -> format1 "%s" (aux n names p)) pats))) |> String.concat "\n" in
        begin match pats, wopt with
            | [[]], None
            | [], None ->  Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders (aux n names body)
            | _ -> Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders (aux n names body) (weightToSmt wopt) pats_str
        end in
    aux 0 [] t


let caption_to_string = function
    | None -> ""
    | Some c ->
        let hd::tl = Util.splitlines c in
        let suffix = match tl with
            | [] -> ""
            | _ -> "..." in
        format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix

let rec declToSmt z3options decl = match decl with
  | DefPrelude -> mkPrelude z3options
  | Caption c ->
    format1 "\n; %s" (Util.splitlines c |> (function [] -> "" | h::t -> h))
  | DeclFun(f,argsorts,retsort,c) ->
    let l = List.map strSort argsorts in
    format4 "%s(declare-fun %s (%s) %s)" (caption_to_string c) f (String.concat " " l) (strSort retsort)
  | DefineFun(f,arg_sorts,retsort,body,c) ->
    let names, binders = name_binders arg_sorts in
    let body = inst (List.map mkFreeV names) body in
    format5 "%s(define-fun %s (%s) %s\n %s)" (caption_to_string c) f (String.concat " " binders) (strSort retsort) (termToSmt body)
  | Assume(t,c) ->
    format2 "%s(assert %s)" (caption_to_string c) (termToSmt t)
  | Eval t ->
    format1 "(eval %s)" (termToSmt t)
  | Echo s ->
    format1 "(echo \"%s\")" s
  | CheckSat -> "(check-sat)"
  | Push -> "(push)"
  | Pop -> "(pop)"

and mkPrelude z3options =
  let basic = z3options ^
                "(declare-sort Ref)\n\
                (declare-fun Ref_constr_id (Ref) Int)\n\
                \n\
                (declare-sort String)\n\
                (declare-fun String_constr_id (String) Int)\n\
                \n\
                (declare-sort Kind)\n\
                (declare-fun Kind_constr_id (Kind) Int)\n\
                \n\
                (declare-sort Type)\n\
                (declare-fun Type_constr_id (Type) Int)\n\
                \n\
                (declare-sort Term)\n\
                (declare-fun Term_constr_id (Term) Int)\n\
                (declare-datatypes () ((Fuel \n\
                                        (ZFuel) \n\
                                        (SFuel (prec Fuel)))))\n\
                (declare-fun MaxIFuel () Fuel)\n\
                (declare-fun MaxFuel () Fuel)\n\
                (declare-fun PreKind (Type) Kind)\n\
                (declare-fun PreType (Term) Type)\n\
                (declare-fun Valid (Type) Bool)\n\
                (declare-fun HasKind (Type Kind) Bool)\n\
                (declare-fun HasTypeFuel (Fuel Term Type) Bool)\n\
                (define-fun HasTypeZ ((x Term) (t Type)) Bool\n\
                    (HasTypeFuel ZFuel x t))\n\
                (define-fun HasType ((x Term) (t Type)) Bool\n\
                    (HasTypeFuel MaxIFuel x t))\n\
                ;;fuel irrelevance\n\
                (assert (forall ((f Fuel) (x Term) (t Type))\n\
		                (! (= (HasTypeFuel (SFuel f) x t)\n\
			                  (HasTypeZ x t))\n\
		                   :pattern ((HasTypeFuel (SFuel f) x t)))))\n\
                (define-fun  IsTyped ((x Term)) Bool\n\
                    (exists ((t Type)) (HasTypeZ x t)))\n\
                (declare-fun ApplyEF (Term Fuel) Term)\n\
                (declare-fun ApplyEE (Term Term) Term)\n\
                (declare-fun ApplyET (Term Type) Term)\n\
                (declare-fun ApplyTE (Type Term) Type)\n\
                (declare-fun ApplyTT (Type Type) Type)\n\
                (declare-fun Rank (Term) Int)\n\
                (declare-fun Closure (Term) Term)\n\
                (declare-fun ConsTerm (Term Term) Term)\n\
                (declare-fun ConsType (Type Term) Term)\n\
                (declare-fun ConsFuel (Fuel Term) Term)\n\
                (declare-fun Precedes (Term Term) Type)\n\
                (assert (forall ((t Type))\n\
                            (! (implies (exists ((e Term)) (HasType e t))\n\
                                        (Valid t))\n\
                                :pattern ((Valid t)))))\n\
                (assert (forall ((t1 Term) (t2 Term))\n\
                     (! (iff (Valid (Precedes t1 t2)) \n\
                             (< (Rank t1) (Rank t2)))\n\
                        :pattern ((Precedes t1 t2)))))\n\
                (define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n\
                         (Precedes t1 t2))\n" in
   let constrs : constructors = [("String_const", ["String_const_proj_0", Int_sort], String_sort, 0);
                                 ("Kind_type",  [], Kind_sort, 0);
                                 ("Kind_arrow", ["Kind_arrow_id", Int_sort], Kind_sort, 1);
                                 ("Kind_uvar",  [("Kind_uvar_fst", Int_sort)], Kind_sort, 2);
                                 ("Typ_fun",    ["Typ_fun_id", Int_sort], Type_sort, 1);
                                 ("Typ_app",    [("Typ_app_fst", Type_sort);
                                                 ("Typ_app_snd", Type_sort)], Type_sort, 2);
                                 ("Typ_dep",    [("Typ_dep_fst", Type_sort);
                                                 ("Typ_dep_snd", Term_sort)], Type_sort, 3);
                                 ("Typ_uvar",   [("Typ_uvar_fst", Int_sort)], Type_sort, 4);
                                 ("Term_unit",  [], Term_sort, 0);
                                 ("BoxInt",     ["BoxInt_proj_0", Int_sort], Term_sort, 1);
                                 ("BoxBool",    ["BoxBool_proj_0", Bool_sort], Term_sort, 2);
                                 ("BoxString",  ["BoxString_proj_0", String_sort], Term_sort, 3);
                                 ("BoxRef",     ["BoxRef_proj_0", Ref_sort], Term_sort, 4);
                                 ("Exp_uvar",   [("Exp_uvar_fst", Int_sort)], Term_sort, 5);
                                 ("LexCons",    [("LexCons_0", Term_sort); ("LexCons_1", Term_sort)], Term_sort, 6)] in
   let bcons = constrs |> List.collect constructor_to_decl |> List.map (declToSmt z3options) |> String.concat "\n" in
   let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n\
                                   (is-LexCons t))\n\
                       (assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n\
                                    (iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n\
                                         (or (Valid (Precedes x1 y1))\n\
                                             (and (= x1 y1)\n\
                                                  (Valid (Precedes x2 y2)))))))\n" in
   basic ^ bcons ^ lex_ordering

let mk_Kind_type        = mkApp("Kind_type", [])
let mk_Kind_uvar i      = mkApp("Kind_uvar", [mkInteger'  i])
let mk_Typ_app t1 t2    = mkApp("Typ_app", [t1;t2])
let mk_Typ_dep t1 t2    = mkApp("Typ_dep", [t1;t2])
let mk_Typ_uvar i       = mkApp("Typ_uvar", [mkInteger' i])
let mk_Exp_uvar i       = mkApp("Exp_uvar", [mkInteger' i])

let mk_Term_unit        = mkApp("Term_unit", [])
let boxInt t            = mkApp("BoxInt", [t])
let unboxInt t          = mkApp("BoxInt_proj_0", [t])
let boxBool t           = mkApp("BoxBool", [t])
let unboxBool t         = mkApp("BoxBool_proj_0", [t])
let boxString t         = mkApp("BoxString", [t])
let unboxString t       = mkApp("BoxString_proj_0", [t])
let boxRef t            = mkApp("BoxRef", [t])
let unboxRef t          = mkApp("BoxRef_proj_0", [t])
let boxTerm sort t = match sort with
  | Int_sort -> boxInt t
  | Bool_sort -> boxBool t
  | String_sort -> boxString t
  | Ref_sort -> boxRef t
  | _ -> raise Impos
let unboxTerm sort t = match sort with
  | Int_sort -> unboxInt t
  | Bool_sort -> unboxBool t
  | String_sort -> unboxString t
  | Ref_sort -> unboxRef t
  | _ -> raise Impos

let mk_PreKind t      = mkApp("PreKind", [t])
let mk_PreType t      = mkApp("PreType", [t])
let mk_Valid t        = match t.tm with 
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_Equality", [_; t1; t2])}]) -> mkEq (t1, t2)
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_disEquality", [_; t1; t2])}]) -> mkNot (mkEq (t1, t2))
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_LessThanOrEqual", [t1; t2])}]) -> mkLTE (unboxInt t1, unboxInt t2)
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_LessThan", [t1; t2])}]) -> mkLT (unboxInt t1, unboxInt t2)
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_GreaterThanOrEqual", [t1; t2])}]) -> mkGTE (unboxInt t1, unboxInt t2)
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_GreaterThan", [t1; t2])}]) -> mkGT (unboxInt t1, unboxInt t2)
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_AmpAmp", [t1; t2])}]) -> mkAnd (unboxBool t1, unboxBool t2)
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_BarBar", [t1; t2])}]) -> mkOr (unboxBool t1, unboxBool t2)
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_Negation", [t])}]) -> mkNot (unboxBool t)
    | App(Var "Prims.b2t", [t]) -> unboxBool t
    | _ -> mkApp("Valid",   [t])
let mk_HasType v t    = mkApp("HasType", [v;t])
let mk_HasTypeZ v t   = mkApp("HasTypeZ", [v;t])
let mk_IsTyped v      = mkApp("IsTyped", [v])
let mk_HasTypeFuel f v t =
   if !Options.unthrottle_inductives
   then mk_HasType v t
   else mkApp("HasTypeFuel", [f;v;t])
let mk_HasTypeWithFuel f v t = match f with
    | None -> mk_HasType v t
    | Some f -> mk_HasTypeFuel f v t
let mk_Destruct v     = mkApp("Destruct", [v])
let mk_HasKind t k    = mkApp("HasKind", [t;k])
let mk_Rank x         = mkApp("Rank", [x])
let mk_tester n t     = mkApp("is-"^n,   [t])
let mk_ApplyTE t e    = mkApp("ApplyTE", [t;e])
let mk_ApplyTT t t'   = mkApp("ApplyTT", [t;t'])
let mk_ApplyET e t    = mkApp("ApplyET", [e;t])
let mk_ApplyEE e e'   = mkApp("ApplyEE", [e;e'])
let mk_ApplyEF e f    = mkApp("ApplyEF", [e;f])
let mk_String_const i = mkApp("String_const", [ mkInteger' i])
let mk_Precedes x1 x2 = mkApp("Precedes", [x1;x2]) |> mk_Valid
let mk_LexCons x1 x2  = mkApp("LexCons", [x1;x2])
let rec n_fuel n =
    if n = 0 then mkApp("ZFuel", [])
    else mkApp("SFuel", [n_fuel (n - 1)])
let fuel_2 = n_fuel 2
let fuel_100 = n_fuel 100

let mk_and_opt p1 p2 = match p1, p2  with
  | Some p1, Some p2 -> Some (mkAnd(p1, p2))
  | Some p, None
  | None, Some p -> Some p
  | None, None -> None

let mk_and_opt_l pl =
  List.fold_left (fun out p -> mk_and_opt p out) None pl

let mk_and_l l = match l with
  | [] -> mkTrue
  | hd::tl -> List.fold_left (fun p1 p2 -> mkAnd(p1,p2)) hd tl

let mk_or_l l = match l with
  | [] -> mkFalse
  | hd::tl -> List.fold_left (fun p1 p2 -> mkOr(p1,p2)) hd tl


let rec print_smt_term (t:term) :string = match t.tm with
  | Integer n               -> Util.format1 "Integer %s" n
  | BoundV  n               -> Util.format1 "BoundV %s" (Util.string_of_int n)
  | FreeV  fv               -> Util.format1 "FreeV %s" (fst fv)
  | App (op, l)             -> Util.format2 "App %s [ %s ]" (op_to_string op) (print_smt_term_list l)
  | Quant (qop, l, _, _, t) -> Util.format3 "Quant %s %s %s" (qop_to_string qop) (print_smt_term_list_list l) (print_smt_term t)

and print_smt_term_list (l:list<term>) :string = List.fold_left (fun s t -> (s ^ "; " ^ (print_smt_term t))) "" l

and print_smt_term_list_list (l:list<list<term>>) :string =
    List.fold_left (fun s l -> (s ^ "; [ " ^ (print_smt_term_list l) ^ " ] ")) "" l
