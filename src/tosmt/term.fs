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

module Microsoft.FStar.ToSMT.Term

open System.Diagnostics
open Microsoft.FStar
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn
open Microsoft.FStar.Util

type sort =
  | Bool_sort 
  | Int_sort 
  | Kind_sort 
  | Type_sort 
  | Term_sort 
  | String_sort
  | Ref_sort
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
  | Array(s1, s2) -> format2 "(Array %s %s)" (strSort s1) (strSort s2)
  | Arrow(s1, s2) -> format2 "(%s -> %s)" (strSort s1) (strSort s2)
  | Sort s -> s

type term' =
  | True
  | False
  | Integer    of int
  | BoundV     of string * sort 
  | FreeV      of string * sort
  | PP         of term * term
  | App        of string * list<term>
  | Not        of term
  | And        of list<term>
  | Or         of list<term>
  | Imp        of term * term
  | Iff        of term * term
  | Eq         of term * term
  | LT         of term * term
  | LTE        of term * term
  | GT         of term * term
  | GTE        of term * term
  | Add        of term * term
  | Sub        of term * term
  | Div        of term * term
  | Mul        of term * term
  | Minus      of term
  | Mod        of term * term
  | ITE        of term * term * term 
  | Forall     of list<list<pat>> * option<int> * list<(string * sort)> * term 
  | Exists     of list<list<pat>> * option<int> * list<(string * sort)> * term 
  | Select     of term * term 
  | Update     of term * term * term
  | ConstArray of string * sort * term 
  | Cases      of list<term>
and pat = term
and term = {tm:term'; as_str:string; freevars:Syntax.memo<list<var>>}
and var = (string * sort)

(*****************************************************)
(* free variables in a term *)
(*****************************************************)
let rec freevars t = match t.tm with
  | True
  | False
  | Integer _ 
  | FreeV _ -> []
  
  | BoundV(x,y) -> [(x,y)]
  
  | ConstArray(_, _, t)
  | Minus t
  | Not t
  | PP(_, t) -> freevars t

  | Cases tms
  | And tms
  | Or tms
  | App(_, tms) -> List.collect freevars tms
  
  | Imp(t1, t2)
  | Iff(t1, t2)
  | Eq(t1, t2) 
  | LT(t1, t2)
  | LTE(t1, t2)
  | GT(t1, t2)
  | GTE(t1, t2)
  | Add(t1, t2)
  | Sub(t1, t2)
  | Div(t1, t2)
  | Mul(t1, t2)
  | Select(t1, t2)
  | Mod(t1, t2) -> freevars t1 @ freevars t2

  | ITE   (t1, t2, t3)
  | Update(t1, t2, t3) -> freevars t1@freevars t2@freevars t3

  | Forall (_, _, binders, t) 
  | Exists (_, _, binders, t) -> 
    freevars t |> List.filter (fun (x, _) -> binders |> Util.for_all (fun (y, _) -> x<>y))

let free_variables t = match !t.freevars with 
    | Some b -> b
    | None -> 
      let fvs = Util.remove_dups (fun (x, _) (y, _) -> x = y) (freevars t) in
      t.freevars := Some fvs;
      fvs
 
(*****************************************************)
(* Pretty printing terms and decls in SMT Lib format *)
(*****************************************************)
let termToSmt t = t.as_str
let boundvar_prefix = "@"
let weightToSmt = function
    | None -> ""
    | Some i -> Util.format1 ":weight %s\n" (string_of_int i)
let rec term'ToSmt tm = 
     match tm with
      | True          -> "true"
      | False         -> "false"
      | Integer i     -> 
        if i < 0 then Util.format1 "(- %s)" (string_of_int (-i)) 
        else string_of_int i
      | PP(_,q) -> 
        termToSmt q
      | BoundV(x,_) -> boundvar_prefix ^ x
      | FreeV(x,_)  -> x
      | App(f,[]) -> f
      | App(f,es)     -> 
        let a = List.map termToSmt es in
        let s = String.concat " " a in
        format2 "(%s %s)" f s
      | Not(x) -> 
        format1 "(not %s)" (termToSmt x)
      | And tms -> 
        format1 "(and %s)" (String.concat "\n" (List.map termToSmt tms))
      | Or tms -> 
        format1 "(or %s)" (String.concat "\n" (List.map termToSmt tms))
      | Imp(x,y) -> 
        format2 "(implies %s\n %s)" (termToSmt x)(termToSmt y)
      | Iff(x,y) -> 
        format2 "(iff %s\n %s)" (termToSmt x) (termToSmt y)
      | Eq(x,y) -> 
        format2 "(= %s\n %s)" (termToSmt x) (termToSmt y)
      | LT(x,y) -> 
        format2 "(< %s %s)" (termToSmt x) (termToSmt y)
      | GT(x,y) -> 
        format2 "(> %s %s)" (termToSmt x) (termToSmt y)
      | LTE(x,y) -> 
        format2 "(<= %s %s)" (termToSmt x) (termToSmt y)
      | GTE(x,y) -> 
        format2 "(>= %s %s)" (termToSmt x) (termToSmt y)
      | Minus(t1) -> 
        format1 "(- %s)" (termToSmt t1)
      | Add(t1,t2) -> 
        format2 "(+ %s\n %s)" (termToSmt t1) (termToSmt t2)
      | Sub(t1,t2) -> 
        format2 "(- %s\n %s)" (termToSmt t1) (termToSmt t2)
      | Mul(t1,t2) -> 
        format2 "(* %s\n %s)" (termToSmt t1) (termToSmt t2)
      | Div(t1,t2) -> 
        format2 "(div %s\n %s)" (termToSmt t1) (termToSmt t2)
      | Mod(t1,t2) -> 
        format2 "(mod %s\n %s)" (termToSmt t1) (termToSmt t2)
      | Select(h,l) -> 
        format2 "(select %s %s)" (termToSmt h) (termToSmt l)
      | Update(h,l,v) -> 
        format3 "(store %s %s %s)" (termToSmt h) (termToSmt l) (termToSmt v)
      | ITE(t1, t2, t3) -> 
        format3 "(ite %s\n\t%s\n\t%s)" (termToSmt t1) (termToSmt t2) (termToSmt t3)
      | Cases tms -> 
        format1 "(and %s)" (String.concat " " (List.map termToSmt tms))
      | Forall(pats,wopt,binders',z)
      | Exists(pats,wopt,binders',z) -> 
        let patsToSmt = function 
          | [] -> ""
          | pats -> format1 "\n:pattern (%s)" (String.concat " " (List.map (fun p -> format1 "%s" (termToSmt p)) pats)) in
        let strQuant = function 
          | Forall _ -> "forall"
          | _ -> "exists"  in
        let s = binders' |> 
                List.map (fun (a,b) -> format3 "(%s%s %s)" boundvar_prefix a (strSort b)) |>
                String.concat " " in
            format3 "(%s (%s)\n %s)" (strQuant tm) s
            (if pats |> Util.for_some (function [] -> false | _ -> true) || Option.isSome wopt
             then format3 "(! %s\n %s %s)" (termToSmt z) (weightToSmt wopt) (pats |> List.map patsToSmt |> String.concat "\n")
             else termToSmt z)
      | ConstArray(s, _, tm) -> 
        format2 "((as const %s) %s)" s (termToSmt tm)

let eq_var (x1, _) (x2, _) = x1=x2
let third (_, _, x) = x
let all_terms = Util.smap_create<term> 10000
let mk t = 
    let key = term'ToSmt t in
    match Util.smap_try_find all_terms key with 
        | Some tm -> tm 
        | None -> 
            let tm = {tm=t; as_str=key; freevars=Util.mk_ref None} in
            Util.smap_add all_terms key tm;
            tm

let freeV_sym fv = match fv.tm with 
    | FreeV(s, _) -> s
    | _ -> failwith "Not a free variable"
let boundV_sym x = match x.tm with 
    | BoundV(x, _) -> x
    | _ -> failwith "Not a bound variable"

let mkTrue       = mk True 
let mkFalse      = mk False
let mkInteger i  = mk (Integer i) 
let mkBoundV i   = mk (BoundV i) 
let mkFreeV x    = mk (FreeV x) 
let mkPP  t      = mk (PP t) 
let mkApp f      = mk (App f) 
let mkNot t      = match t.tm with
    | True -> mkFalse
    | False -> mkTrue
    | _ -> mk (Not t) 
let mkAnd (t1, t2)  = match t1.tm, t2.tm with 
    | True, _ -> t2
    | _, True -> t1
    | False, _
    | _, False -> mkFalse
    | And ts1, And ts2 -> mk (And (ts1@ts2))
    | _, And ts2 -> mk (And(t1::ts2))
    | And ts1, _ -> mk (And(ts1@[t2]))
    | _ -> mk (And [t1;t2]) 
let mkOr (t1, t2)  = match t1.tm, t2.tm with 
    | True, _ 
    | _, True -> mkTrue
    | False, _ -> t2
    | _, False -> t1
    | Or ts1, Or ts2 -> mk (Or (ts1@ts2))
    | _, Or ts2 -> mk (Or(t1::ts2))
    | Or ts1, _ -> mk (Or(ts1@[t2]))
    | _ -> mk (Or [t1;t2]) 
let rec mkImp (t1, t2) = match t1.tm, t2.tm with 
    | _, True -> mkTrue
    | True, _ -> t2
    | _, Imp(t1', t2') -> mkImp(mkAnd(t1, t1'), t2')
    | _ -> mk (Imp(t1, t2)) 
let mkIff t      = mk (Iff t)
let mkEq t       = mk (Eq t) 
let mkLT t       = mk (LT t) 
let mkLTE t      = mk (LTE t)
let mkGT t       = mk (GT t) 
let mkGTE t      = mk (GTE t)
let mkAdd t      = mk (Add t)
let mkSub t      = mk (Sub t)
let mkDiv t      = mk (Div t)
let mkMul t      = mk (Mul t)
let mkMinus t    = mk (Minus t)
let mkMod t      = mk (Mod t) 
let mkITE t      = mk (ITE t) 
let mkSelect t   = mk (Select t) 
let mkUpdate t   = mk (Update t) 
let mkCases t    = mk (Cases t)  
let mkConstArr t = mk (ConstArray t) 
let mkForall' (pats, wopt, vars, body) = 
    if List.length vars = 0 then body 
    else match body.tm with 
            | True -> body 
            | _ -> mk (Forall(pats,wopt,vars,body)) 
let mkForall (pats, vars, body) = mkForall'([pats], None, vars, body)
let mkExists (pats, vars, body) = 
    if List.length vars = 0 then body 
    else match body.tm with 
            | True -> body 
            | _ -> mk (Exists([pats],None,vars,body)) 


type caption = option<string>
type binders = list<(string * sort)>
type projector = (string * sort)
type constructor_t = (string * list<projector> * sort * int)
type constructors  = list<constructor_t>
type decl =
  | DefPrelude
  | DeclFun    of string * list<sort> * sort * caption
  | DefineFun  of string * list<(string * sort)> * sort * term * caption
  | Assume     of term   * caption
  | Caption    of string
  | Eval       of term
  | Echo       of string
  | Push
  | Pop
  | CheckSat
type decls_t = list<decl>

let constr_id_of_sort sort = format1 "%s_constr_id" (strSort sort)
let constructor_to_decl_aux disc_inversion (name, projectors, sort, id) =
    let cdecl = DeclFun(name, projectors |> List.map snd, sort, Some "Constructor") in
    let bvar_name i = "x_" ^ string_of_int i in
    let bvar i s = mkBoundV(bvar_name i, s) in
    let bvars = projectors |> List.mapi (fun i (_, s) -> bvar_name i, s) in
    let capp = mkApp(name, bvars |> List.map mkBoundV) in
    let cid_app = mkApp(constr_id_of_sort sort, [capp]) in
    let cid = Assume(mkForall([], bvars, mkEq(mkInteger id, cid_app)), Some "Constructor distinct") in //specifically omitting pattern
    let disc_name = "is-"^name in
    let xx = ("x", sort) in 
    let disc_app = mkApp(disc_name, [mkBoundV xx]) in
//    let disc = DefineFun(disc_name, [xx], Bool_sort, 
//                         mkAnd(mkEq(mkApp(constr_id_of_sort sort, [mkBoundV xx]), mkInteger id),
//                               mkEq(mkBoundV xx, 
//                                    mkApp(name, projectors |> List.map (fun (proj, s) -> mkApp(proj, [mkBoundV xx]))))),
//                         Some "Discriminator definition") in
    let disc_eq = mkEq(mkApp(constr_id_of_sort sort, [mkBoundV xx]), mkInteger id) in
    let proj_terms = projectors |> List.map (fun (proj, s) -> mkApp(proj, [mkBoundV xx])) in
    let disc_inv_body = mkEq(mkBoundV xx, mkApp(name, proj_terms)) in
    let disc_ax = if disc_inversion 
                  then mkAnd(disc_eq, disc_inv_body) 
                  else disc_eq in
    let disc = DefineFun(disc_name, [xx], Bool_sort, 
                         disc_ax,
                         Some "Discriminator definition") in


    let disc_inv_ax = 
        if disc_inversion 
        then []
        else let destruct_pat = match sort with Type_sort -> [] | _ -> [mkApp("Destruct", [mkBoundV xx])] in
              [Assume(mkForall'(destruct_pat::(proj_terms |> List.map (fun x -> [x])), 
                                None,
                                [xx], 
                                mkImp(disc_eq, disc_inv_body)), Some ("guarded inversion equality: " ^ name))] in
    let projs = projectors |> List.mapi (fun i (name, s) -> 
        let cproj_app = mkApp(name, [capp]) in
        [DeclFun(name, [sort], s, Some "Projector");
         Assume(mkForall([capp], bvars, mkEq(cproj_app, bvar i s)), Some "Projection inverse")]) |> List.flatten in
//    let disc_proj = Assume(mkForall([], [xx], mkImp(disc_app, 
//                                                    mkEq(mkBoundV xx, 
//                                                         mkApp(name, projectors |> List.map (fun (proj, s) -> mkApp(proj, [mkBoundV xx])))))), Some "Disc/Proj correspondence") in
    Caption (format1 "<start constructor %s>" name)::cdecl::cid::projs@[disc]@disc_inv_ax@[Caption (format1 "</end constructor %s>" name)]

let constructor_to_decl f = constructor_to_decl_aux true f
      
(****************************************************************************)
(* Standard SMTLib prelude for F* and some term constructors                *)
(****************************************************************************)
let caption_to_string = function 
    | None -> ""
    | Some c -> format1 ";;;;;;;;;;;;;;;;%s\n" c

let rec declToSmt z3options decl = match decl with
  | DefPrelude -> mkPrelude z3options
  | Caption c -> 
    format1 "\n; %s" c
  | DeclFun(f,argsorts,retsort,c) ->
    let l = List.map strSort argsorts in
    format4 "%s(declare-fun %s (%s) %s)" (caption_to_string c) f (String.concat " " l) (strSort retsort)
  | DefineFun(f,args,retsort,body,c) ->
    let l = List.map (fun (nm,s) -> format3 "(%s%s %s)" boundvar_prefix nm (strSort s)) args in
    format5 "%s(define-fun %s (%s) %s\n %s)" (caption_to_string c) f (String.concat " " l) (strSort retsort) (termToSmt body)
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
                (declare-fun ZFuel () Term)\n\
                (declare-fun SFuel (Term) Term)\n\
                (declare-fun MaxFuel () Term)\n\
                (declare-fun PreKind (Type) Kind)\n\
                (declare-fun PreType (Term) Type)\n\
                (declare-fun Valid (Type) Bool)\n\
                (declare-fun HasKind (Type Kind) Bool)\n\
                (declare-fun HasType (Term Type) Bool)\n\
                (declare-fun ApplyEE (Term Term) Term)\n\
                (declare-fun ApplyET (Term Type) Term)\n\
                (declare-fun ApplyTE (Type Term) Type)\n\
                (declare-fun ApplyTT (Type Type) Type)\n\
                (declare-fun Rank (Term) Int)\n\
                (declare-fun Closure (Term) Term)\n\
                (declare-fun ConsTerm (Term Term) Term)\n\
                (declare-fun ConsType (Type Term) Term)\n\
                (declare-fun Precedes (Term Term) Type)\n\
                (assert (forall ((t1 Term) (t2 Term))\n\
                     (! (iff (Valid (Precedes t1 t2)) \n\
                             (< (Rank t1) (Rank t2)))\n\
                        :pattern ((Precedes t1 t2)))))\n\
                (define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n\
                         (Precedes t1 t2))\n" in
   let constrs : constructors = [("String_const", ["String_const_proj_0", Int_sort], String_sort, 0);
                                 ("Kind_type",  [], Kind_sort, 0);
                                 ("Kind_arrow", ["Kind_arrow_id", Int_sort], Kind_sort, 1);
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
                                 ("LexCons",    [("LexCons_0", Term_sort); ("LexCons_1", Term_sort)], Term_sort, 5)] in
   let bcons = constrs |> List.collect (constructor_to_decl_aux true) |> List.map (declToSmt z3options) |> String.concat "\n" in
   let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n\
                                   (is-LexCons t))\n\
                       (assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n\
                                    (iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n\
                                         (or (Valid (Precedes x1 y1))\n\
                                             (and (= x1 y1)\n\
                                                  (Valid (Precedes x2 y2)))))))\n" in
   basic ^ bcons ^ lex_ordering

let mk_Kind_type        = mkApp("Kind_type", [])
let mk_Typ_app t1 t2    = mkApp("Typ_app", [t1;t2])
let mk_Typ_dep t1 t2    = mkApp("Typ_dep", [t1;t2])
let mk_Typ_uvar i       = mkApp("Typ_uvar", [mkInteger i])

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
let mk_Valid t        = mkApp("Valid",   [t])  
//    match t.tm with 
//        | App("Prims.b2t", [v]) -> unboxBool v
//        | _ -> mkApp("Valid",   [t])  
let mk_HasType (b:bool) v t  = 
    mkApp("HasType", [v;t])
let mk_Destruct v     = mkApp("Destruct", [v])
let mk_HasKind t k    = mkApp("HasKind", [t;k])
let mk_Rank x         = mkApp("Rank", [x])
let mk_tester n t     = mkApp("is-"^n,   [t])
let mk_ApplyTE t e    = mkApp("ApplyTE", [t;e])
let mk_ApplyTT t t'   = mkApp("ApplyTT", [t;t'])
let mk_ApplyET e t    = mkApp("ApplyET", [e;t])
let mk_ApplyEE e e'   = mkApp("ApplyEE", [e;e'])
let mk_String_const i = mkApp("String_const", [ mkInteger i ])
let mk_Precedes x1 x2 = mkApp("Precedes", [x1;x2]) |> mk_Valid
let mk_LexCons x1 x2  = mkApp("LexCons", [x1;x2])
let mk_Closure i vars   = 
   let vars = vars |> List.fold_left (fun out v -> match snd v with 
    | Term_sort -> mkApp("ConsTerm", [mkBoundV v; out])
    | Type_sort -> mkApp("ConsType", [mkBoundV v; out])) (boxInt <| mkInteger i) in
    mkApp("Closure", [vars])
let rec n_fuel n = 
    if n = 0 then mkFreeV("ZFuel", Term_sort)
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

