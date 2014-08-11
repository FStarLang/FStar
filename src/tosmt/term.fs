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
  | And        of term * term
  | Or         of term * term
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
  | Forall     of list<pat> * list<(string * sort)> * term 
  | Exists     of list<pat> * list<(string * sort)> * term 
  | Select     of term * term 
  | Update     of term * term * term
  | ConstArray of string * sort * term 
  | Cases      of list<term>
and pat = term
and term = {tm:term'; freevars:ref<fvs_t>}
and fvs_t = 
  | Set of list<var>
  | Delayed of (unit -> list<ref<fvs_t>>)
and var = (string * sort)

let sub_fv l1 l2 = 
  l1 |> List.partition (fun (x, _) -> l2 |> Util.for_some (fun (y, _) -> x=y)) |> snd
let rec claim f = match !f with 
  | Set l -> l
  | Delayed fs -> 
    let l = fs() |> List.fold_left (fun out f -> (sub_fv (claim f) out)@out) [] in
    f := Set l;
    l
let freevars t = claim t.freevars
let third (_, _, x) = x
let fvs t = match !t.freevars with 
  | Set _ -> [t.freevars]
  | Delayed l -> l()
let mk t f = {tm=t; freevars=Util.mk_ref f}
let mk' t f = {tm=t; freevars=f}
let fv_l ts = Delayed (fun () -> ts |> List.fold_left (fun out t -> fvs t@out) [])
let fv_bin (t1,t2) = Delayed (fun () -> fvs t1@fvs t2)
let fv_tri (t1,t2,t3) = Delayed (fun () -> fvs t1@fvs t2@fvs t3)
let fv_minus v u = Set <| sub_fv (claim v) u

let mkTrue       = mk True (Set [])
let mkFalse      = mk False (Set [])
let mkInteger i  = mk (Integer i) (Set [])
let mkBoundV i   = mk (BoundV i) (Set [i])
let mkFreeV x    = mk (FreeV x) (Set [])
let mkPP  t      = mk' (PP t) (snd t).freevars
let mkApp f      = mk (App f) <| fv_l (snd f)
let mkNot t      = mk' (Not t) t.freevars
let mkAnd t      = match t with 
    | {tm=True}, t'
    | t', {tm=True} -> t'
    | {tm=False}, _
    | _, {tm=False} -> mkFalse
    | _ -> mk (And t) <| fv_bin t
let mkOr t        = match t with 
    | {tm=False}, t'
    | t', {tm=False} -> t'
    | {tm=True}, _
    | _, {tm=True} -> mkTrue
    | _ -> mk (Or t)  <| fv_bin t
let mkImp (t1, t2) = match t1.tm, t2.tm with 
    | _, True
    | True, _ -> t2
    | _ -> mk (Imp (t1,t2)) <| fv_bin (t1,t2)
let mkIff t      = mk (Iff t) <| fv_bin t
let mkEq t       = mk (Eq t)  <| fv_bin t
let mkLT t       = mk (LT t)  <| fv_bin t
let mkLTE t      = mk (LTE t) <| fv_bin t
let mkGT t       = mk (GT t)  <| fv_bin t
let mkGTE t      = mk (GTE t) <| fv_bin t
let mkAdd t      = mk (Add t) <| fv_bin t
let mkSub t      = mk (Sub t) <| fv_bin t
let mkDiv t      = mk (Div t) <| fv_bin t
let mkMul t      = mk (Mul t) <| fv_bin t
let mkMinus t    = mk' (Minus t) <| t.freevars
let mkMod t      = mk (Mod t) <| fv_bin t
let mkITE t      = mk (ITE t) <| fv_tri t
let mkSelect t   = mk (Select t) <| fv_bin t
let mkUpdate t   = mk (Update t) <| fv_tri t
let mkCases t    = mk (Cases t)  <| fv_l t
let mkConstArr t = mk' (ConstArray t) <| (third t).freevars
let check_pats pats vars = ()
//    pats |> List.iter (fun p -> 
//        let fvs = claim p.freevars in
//        if vars |> Util.for_all (fun (x,_) -> fvs |> Util.for_some (fun (y, _) -> x=y))
//        then ()
//        else Util.print_string <| Util.format1 "pattern %s misses a bound var" (termToSmt [] p))
let mkForall (pats, vars, body) = 
    check_pats pats vars;
    if List.length vars = 0 then body 
    else match body.tm with 
            | True -> body 
            | _ -> mk (Forall(pats,vars,body)) <| fv_minus body.freevars vars
let collapseForall (pats, vars, body) =
    check_pats pats vars;
    if List.length vars = 0 then body 
    else match body.tm with 
        | True-> body
        | Forall(pats', vars', body') -> mkForall(pats@pats', vars@vars', body')
        | _ -> mkForall(pats, vars, body)
let mkExists (pats, vars, body) = 
    check_pats pats vars;
    if List.length vars = 0 then body 
    else match body.tm with 
            | True -> body 
            | _ -> mk (Exists(pats,vars,body)) <| fv_minus body.freevars vars


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
type decls = list<decl>

let constr_id_of_sort sort = format1 "%s_constr_id" (strSort sort)
let constructor_to_decl (name, projectors, sort, id) =
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
    let disc = DefineFun(disc_name, [xx], Bool_sort, mkEq(mkApp(constr_id_of_sort sort, [mkBoundV xx]), mkInteger id), Some "Discriminator definition") in
    let projs = projectors |> List.mapi (fun i (name, s) -> 
        let cproj_app = mkApp(name, [capp]) in
        [DeclFun(name, [sort], s, Some "Projector");
         Assume(mkForall([(*cproj_app ... specifically omitting pattern *)], bvars, mkEq(cproj_app, bvar i s)), Some "Projection inverse")]) |> List.flatten in
    Caption (format1 "<start constructor %s>" name)::cdecl::cid::disc::projs@[Caption (format1 "</end constructor %s>" name)]

let flatten_imp tm = 
  let mkAnd_l terms = match terms with 
    | [] -> mkTrue
    | [hd] -> hd
    | hd::tl ->  List.fold_left (fun out term -> mkAnd(out, term)) hd tl in
  let rec aux out tm = match tm.tm with
    | Imp({tm=True}, x) -> aux out x
    | Imp(x, y) -> aux (x::out) y
    | _ -> mkAnd_l (List.rev out), tm in
    aux [] tm

let flatten_and tm =
  let rec aux out tm = match tm.tm with 
    | And({tm=True}, x) 
    | And(x, {tm=True}) -> aux out x
    | And(x, y) -> aux (aux out x) y
    | _ -> tm::out in
    List.rev (aux [] tm)
      
let flatten_or tm = 
  let rec aux out tm = match tm.tm with 
    | Or({tm=False}, x)
    | Or(x, {tm=False}) -> aux out x
    | Or(x, y) -> aux (aux out x) y
    | _ -> tm::out in
    List.rev (aux [] tm)


(*****************************************************)
(* Pretty printing terms and decls in SMT Lib format *)
(*****************************************************)
let string_of_either_bvd = function
  | Inl x -> Print.strBvd x
  | Inr x -> Print.strBvd x

let rec termToSmt binders tm = 
     match tm.tm with
      | True          -> "true"
      | False         -> "false"
      | Integer i     -> 
        if i < 0 then Util.format1 "(- %s)" (string_of_int (-i)) 
        else string_of_int i
      | PP(_,q) -> 
        termToSmt binders q
      | BoundV(x,_) 
      | FreeV(x,_)  -> x
      | App(f,[]) -> f
      | App(f,es)     -> 
        let a = List.map (termToSmt binders) es in
        let s = String.concat " " a in
        format2 "(%s %s)" f s
      | Not(x) -> 
        format1 "(not %s)" (termToSmt binders x)
      | And _ -> 
        format1 "(and %s)" (String.concat "\n" (List.map (termToSmt binders) (flatten_and tm)))
      | Or _ -> 
        format1 "(or %s)" (String.concat "\n" (List.map (termToSmt binders) (flatten_or tm)))
      | Imp _ -> 
        let x, y = flatten_imp tm in
        format2 "(implies %s\n %s)"(termToSmt binders x)(termToSmt binders y)
      | Iff(x,y) -> 
        format2 "(iff %s\n %s)" (termToSmt binders x) (termToSmt binders y)
      | Eq(x,y) -> 
        format2 "(= %s\n %s)" (termToSmt binders x) (termToSmt binders y)
      | LT(x,y) -> 
        format2 "(< %s %s)" (termToSmt binders x) (termToSmt binders y)
      | GT(x,y) -> 
        format2 "(> %s %s)" (termToSmt binders x) (termToSmt binders y)
      | LTE(x,y) -> 
        format2 "(<= %s %s)" (termToSmt binders x) (termToSmt binders y)
      | GTE(x,y) -> 
        format2 "(>= %s %s)" (termToSmt binders x) (termToSmt binders y)
      | Minus(t1) -> 
        format1 "(- %s)" (termToSmt binders t1)
      | Add(t1,t2) -> 
        format2 "(+ %s\n %s)" (termToSmt binders t1) (termToSmt binders t2)
      | Sub(t1,t2) -> 
        format2 "(- %s\n %s)" (termToSmt binders t1) (termToSmt binders t2)
      | Mul(t1,t2) -> 
        format2 "(* %s\n %s)" (termToSmt binders t1) (termToSmt binders t2)
      | Div(t1,t2) -> 
        format2 "(div %s\n %s)" (termToSmt binders t1) (termToSmt binders t2)
      | Mod(t1,t2) -> 
        format2 "(mod %s\n %s)" (termToSmt binders t1) (termToSmt binders t2)
      | Select(h,l) -> 
        format2 "(select %s %s)" (termToSmt binders h) (termToSmt binders l)
      | Update(h,l,v) -> 
        format3 "(store %s %s %s)" (termToSmt binders h) (termToSmt binders l) (termToSmt binders v)
      | ITE(t1, t2, t3) -> 
        format3 "(ite %s\n\t%s\n\t%s)" (termToSmt binders t1) (termToSmt binders t2) (termToSmt binders t3)
      | Cases tms -> 
        format1 "(and %s)" (String.concat " " (List.map (termToSmt binders) tms))
      | Forall(pats,binders',z)
      | Exists(pats,binders',z) -> 
        let patsToSmt binders = function 
          | [] -> ""
          | pats -> format1 "\n:pattern (%s)" (String.concat " " (List.map (fun p -> format1 "%s" (termToSmt binders p)) pats)) in
        let strQuant = function 
          | {tm=Forall _} -> "forall"
          | _ -> "exists"  in
        let s = binders' |> 
                List.map (fun (a,b) -> format2 "(%s %s)" a (strSort b)) |>
                String.concat " " in
        let binders' = List.rev binders' @ binders in
            format3 "(%s (%s)\n %s)" (strQuant tm) s
            (if List.length pats <> 0 
                then format2 "(! %s\n %s)" (termToSmt binders' z) (patsToSmt binders' pats)
                else termToSmt binders' z)
      | ConstArray(s, _, tm) -> 
        format2 "((as const %s) %s)" s (termToSmt binders tm)


      
(****************************************************************************)
(* Standard SMTLib prelude for F* and some term constructors                *)
(****************************************************************************)
let caption_to_string = function 
    | None -> ""
    | Some c -> format1 ";;;;;;;;;;;;;;;;%s\n" c

let rec declToSmt decl = match decl with
  | DefPrelude -> mkPrelude ()
  | Caption c -> 
    format1 "\n; %s" c
  | DeclFun(f,argsorts,retsort,c) ->
    let l = List.map strSort argsorts in
    format4 "%s(declare-fun %s (%s) %s)" (caption_to_string c) f (String.concat " " l) (strSort retsort)
  | DefineFun(f,args,retsort,body,c) ->
    let l = List.map (fun (nm,s) -> format2 "(%s %s)" nm (strSort s)) args in
    format5 "%s(define-fun %s (%s) %s\n %s)" (caption_to_string c) f (String.concat " " l) (strSort retsort) (termToSmt (List.rev args) body)
  | Assume(t,c) ->
    format2 "%s(assert %s)" (caption_to_string c) (termToSmt [] t)
  | Eval t -> 
    format1 "(eval %s)" (termToSmt [] t)
  | Echo s -> 
    format1 "(echo \"%s\")" s
  | CheckSat -> "(check-sat)"
  | Push -> "(push)"
  | Pop -> "(pop)"

and mkPrelude () = 
  let basic =  "(set-option :global-decls false)\n\
                (declare-sort Ref)\n\
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
                \n\
                (declare-fun PreKind (Type) Kind)\n\
                (declare-fun PreType (Term) Type)\n\
                (declare-fun Valid (Type) Bool)\n\
                (declare-fun HasKind (Type Kind) Bool)\n\
                (declare-fun HasType (Term Type) Bool)\n\
                (declare-fun ApplyEE (Term Term) Term)\n\
                (declare-fun ApplyET (Term Type) Term)\n\
                (declare-fun ApplyTE (Type Term) Type)\n\
                (declare-fun ApplyTT (Type Type) Type)\n" in
   let constrs : constructors = [("String_const", ["String_const_proj_0", Int_sort], String_sort, 0);
                                 ("Kind_type", [], Kind_sort, 0);
                                 ("Kind_dcon", ["Kind_dcon_id", Int_sort], Kind_sort, 1);
                                 ("Kind_tcon", ["Kind_tcon_id", Int_sort], Kind_sort, 2);
                                 ("Typ_fun",   ["Typ_fun_id", Int_sort], Type_sort, 1);
                                 ("Typ_app",   [("Typ_app_fst", Type_sort);
                                                ("Typ_app_snd", Type_sort)], Type_sort, 2);
                                 ("Typ_dep",   [("Typ_dep_fst", Type_sort);
                                                ("Typ_dep_snd", Term_sort)], Type_sort, 3);
                                 ("Term_unit", [], Term_sort, 0);
                                 ("BoxInt",    ["BoxInt_proj_0", Int_sort], Term_sort, 1);
                                 ("BoxBool",   ["BoxBool_proj_0", Bool_sort], Term_sort, 2);
                                 ("BoxString", ["BoxString_proj_0", String_sort], Term_sort, 3);
                                 ("BoxRef",    ["BoxRef_proj_0", Ref_sort], Term_sort, 4)] in
   let bcons = constrs |> List.collect constructor_to_decl |> List.map declToSmt |> String.concat "\n" in
   basic ^ bcons 

let mk_Kind_type        = mkApp("Kind_type", [])
let mk_Typ_app t1 t2    = mkApp("Typ_app", [t1;t2])
let mk_Typ_dep t1 t2    = mkApp("Typ_dep", [t1;t2])

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
let mk_HasType v t    = mkApp("HasType", [v;t])
let mk_HasKind t k    = mkApp("HasKind", [t;k])
let mk_tester n t     = mkApp("is-"^n,   [t])
let mk_ApplyTE t e    = mkApp("ApplyTE", [t;e])
let mk_ApplyTT t t'   = mkApp("ApplyTT", [t;t'])
let mk_ApplyET e t    = mkApp("ApplyET", [e;t])
let mk_ApplyEE e e'   = mkApp("ApplyEE", [e;e'])
let mk_String_const i = mkApp("String_const", [ mkInteger i ])

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
