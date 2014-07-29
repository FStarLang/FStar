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
  | Ext of string
  
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
  | Ext s -> s

type term' =
  | True
  | False
  | Integer    of int
  | BoundV     of int * sort * string 
  | FreeV      of string * sort
  | PP         of term * term
  | App        of string * sort * list<term>
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
let mkBoundV i   = mk (BoundV i) (Set [])
let mkFreeV x    = mk (FreeV x) (Set [x])
let mkPP  t      = mk' (PP t) (snd t).freevars
let mkApp f      = mk (App f) <| fv_l (third f)
let mkNot t      = mk' (Not t) t.freevars
let mkAnd t      = mk (And t) <| fv_bin t
let mkOr t       = mk (Or t)  <| fv_bin t
let mkImp t      = mk (Imp t) <| fv_bin t
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
let mkForall (pats, vars, body) = mk (Forall(pats,vars,body)) <| fv_minus body.freevars vars
let mkExists (pats, vars, body) = mk (Exists(pats,vars,body)) <| fv_minus body.freevars vars

type caption = option<string>
type binders = list<(string * sort)>
type typenames = list<string>
type projector = (string * sort)
type datacon   = (string * list<projector> * sort)
type datacons  = list<datacon>
type decl =
  | DefPrelude of typenames * datacons
  | DeclFun    of string * list<sort> * sort * caption
  | DefineFun  of string * list<(string * sort)> * sort * term * caption
  | Assume     of term   * caption
  | Caption    of string
  | Eval       of term
  | Echo       of string
type decls = list<decl>

let rec termEq (x:term) (y:term) =
  match x.tm, y.tm with 
    | PP(a, _), _ -> termEq a y
    | _, PP(b, _) -> termEq x b
    | True, True
    | False, False -> true
    | Integer i, Integer j -> i=j
    | BoundV(i, s, _), BoundV(j, t, _) -> i=j  && s=t
    | FreeV(x,s), FreeV(y,t) -> x=y && s=t
    | App(f,_,tl), App(g,_,sl) when (List.length tl = List.length sl) -> 
        f=g && (List.forall2 termEq tl sl)
    | Minus(t), Minus(s)
    | Not(t), Not(s) -> termEq t (s)
    | And(t1,t2), And(s1,s2)
    | Imp(t1,t2), Imp(s1,s2)
    | Iff(t1,t2), Iff(s1,s2)
    | Or(t1,t2), Or(s1,s2)
    | Eq(t1,t2), Eq(s1,s2)
    | LT(t1,t2), LT(s1,s2)
    | GT(t1,t2), GT(s1,s2)
    | GTE(t1,t2), GTE(s1,s2) 
    | Add(t1,t2), Add(s1,s2) 
    | Sub(t1,t2), Sub(s1,s2) 
    | Mul(t1,t2), Mul(s1,s2) 
    | Div(t1,t2), Div(s1,s2) 
    | Mod(t1,t2), Mod(s1,s2) 
    | Select(t1,t2), Select(s1,s2) -> termEq t1 (s1) && termEq t2 (s2)
    | Update(t1,t2,t3), Update(s1,s2,s3)
    | ITE(t1, t2, t3), ITE(s1, s2, s3) ->
        termEq t1 (s1) && termEq t2 (s2) && termEq t3 (s3)
    | Forall(pl, sorts, t), Forall(ql, sorts', s) 
    | Exists(pl, sorts, t), Forall(ql, sorts', s) -> 
        (List.forall2 termEq pl ql) &&
        sorts=sorts' &&
        termEq t (s)
    | ConstArray(str, sort, t), ConstArray(str', sort', s) -> 
        termEq t (s) && str=str' && sort=sort'
    | Cases(tl), Cases(sl) when (List.length tl = List.length sl) -> 
        List.forall2 termEq tl sl
    | _ -> false

let flatten_imp tm = 
  let mkAnd_l terms = match terms with 
    | [] -> mkTrue
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
      | BoundV(i,_,nm) -> 
        if (i < List.length binders) 
        then nm
        else failwith "Bad index for bound variable in formula" 
      | FreeV(x,_)    -> x
      | App(f,_,[]) -> f
      | App(f,_, es)     -> 
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
        format3 "(ite %s %s %s)" (termToSmt binders t1) (termToSmt binders t2) (termToSmt binders t3)
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
        let s = binders |> 
                List.map (fun (a,b) -> format2 "(%s %s)" a (strSort b)) |>
                String.concat " " in
        let binders' = List.rev binders' @ binders in
            format3 "\n\n(%s (%s)\n\n %s)" (strQuant tm) s
            (if List.length pats <> 0 
                then format2 "(! %s\n %s)" (termToSmt binders' z) (patsToSmt binders' pats)
                else termToSmt binders' z)
      | ConstArray(s, _, tm) -> 
        format2 "((as const %s) %s)" s (termToSmt binders tm)
      
(****************************************************************************)
(* Standard SMTLib prelude for F* and some term constructors                *)
(****************************************************************************)
let mkPrelude typenames datacons = 
 format2 "(declare-sort Ref)\n \
          (declare-datatypes () ((String (String_const (String_const_proj_0 Int))))) \n \
          (declare-datatypes () ((Type_name (Typ_name_other (Type_name_other_id Int)) \n \
                                             %s))) \n \
          (declare-datatypes () ((Kind (Kind_type) \n \
                                       (Kind_dcon (Kind_dcon_id Int)) \n \
                                       (Kind_tcon (Kind_tcon_id Int))) \n \
                                 (Type (Typ_other (Typ_other_id Int)) \n \
                                       (Typ_const (Typ_const_fst Type_name)) \n \
                                       (Typ_fun (Typ_fun_id Int)) \n \
                                       (Typ_univ (Typ_univ_id Int)) \n \
                                       (Typ_app (Typ_app_fst Type) (Typ_app_snd Type)) \n \
                                       (Typ_dep (Typ_dep_fst Type) (Typ_dep_snd Term))) \n \
                                 (Term (Term_other (Term_other_id Int)) \n \
                                       (Term_unit) \n \
                                       (BoxInt (BoxInt_proj_0 Int)) \n \
                                       (BoxBool (BoxBool_proj_0 Bool)) \n \
                                       (BoxString (BoxString_proj_0 String)) \n \
                                       (BoxRef (BoxRef_proj_0 Ref)) \n \
                                       %s)))\n \
          (declare-fun PreKind (Type) Kind)\n \
          (declare-fun PreType (Term) Type)\n \
          (declare-fun Valid (Type) Bool)\n \
          (declare-fun ApplyEE (Term Term) Term)\n \
          (declare-fun ApplyET (Term Type) Term)\n \
          (declare-fun ApplyTE (Type Term) Type)\n \
          (declare-fun ApplyTT (Type Type) Type)\n \
          ;;;;;;;;;;; (Unit typing)\n \
          (assert (= (TypeOf (Term_unit)\n \
                             (Typ_const Type_name_Prims.unit))))\n \
          ;;;;;;;;;;; (Bool typing)\n \
          (assert (forall ((x Term))\n \
                          (implies (is-BoxBool x)\n \
                                   (= (TypeOf x)\n \
                                      (Typ_const Type_name_Prims.bool)))))\n \
          ;;;;;;;;;;; (Int typing)\n \
          (assert (forall ((x Term))\n \
                          (implies (is-BoxInt x)\n \
                                   (= (TypeOf x)\n \
                                      (Typ_const Type_name_Prims.int)))))\n \
          ;;;;;;;;;;; (String typing)\n \
          (assert (forall ((x Term))\n \
                          (iff (is-BoxString x)\n \
                               (= (TypeOf x)\n \
                                  (Typ_const Type_name_Prims.string)))))"
         (typenames |> List.map (fun s -> format1 "\t\t(%s)" s) |>  String.concat "\n") 
         (datacons |> List.map (fun (nm, projs, _) -> 
            format2 "\t\t(%s %s)" nm (projs |> List.map (fun (nm, sort) -> 
                                                            format2 "(%s %s)" nm (strSort sort)) |> String.concat " ")) |> 
          String.concat "\n")

let declToSmt decl = match decl with
  | DefPrelude (tys, datas) -> 
    mkPrelude tys datas
  | Caption c -> 
    format1 "\n; %s" c
  | DeclFun(f,argsorts,retsort,_) ->
    let l = List.map strSort argsorts in
    format3 "(declare-fun %s (%s) %s)" f (String.concat " " l) (strSort retsort)
  | DefineFun(f,args,retsort,body,_) ->
    let l = List.map (fun (nm,s) -> format2 "(%s %s)" nm (strSort s)) args in
    format4 "(define-fun %s (%s) %s\n %s)" f (String.concat " " l) (strSort retsort) (termToSmt (List.rev args) body)
  | Assume(t,co) ->
    let c = match co with 
      | Some c -> format1 ";;;;;;;;;;; %s\n" c
      | None -> "" in 
    format2 "%s (assert %s)" c (termToSmt [] t)
  | Eval t -> 
    format1 "(eval %s)" (termToSmt [] t)
  | Echo s -> 
    format1 "(echo \"%s\")" s

let mk_Kind_type        = mkApp("Kind_type", Kind_sort, [])
let mk_Typ_const n      = mkApp("Typ_const", Arrow(Ext "Type_name", Type_sort), [mkApp(n, Ext "Type_name", [])])
let mk_Typ_app t1 t2    = mkApp("Typ_app", Arrow(Type_sort, Arrow(Type_sort, Type_sort)), [t1;t2])
let mk_Typ_dep t1 t2    = mkApp("Typ_dep", Arrow(Type_sort, Arrow(Term_sort, Type_sort)), [t1;t2])

let mk_Term_unit        = mkApp("Term_unit", Term_sort, [])
let boxInt t            = mkApp("BoxInt", Arrow(Int_sort, Term_sort), [t]) 
let unboxInt t          = mkApp("BoxInt_proj_0", Arrow(Term_sort, Int_sort), [t]) 
let boxBool t           = mkApp("BoxBool", Arrow(Bool_sort, Term_sort), [t]) 
let unboxBool t         = mkApp("BoxBool_proj_0", Arrow(Term_sort, Bool_sort), [t]) 
let boxString t         = mkApp("BoxString", Arrow(String_sort, Term_sort), [t]) 
let unboxString t       = mkApp("BoxString_proj_0", Arrow(Term_sort, String_sort), [t]) 
let boxRef t            = mkApp("BoxRef", Arrow(Ref_sort, Term_sort), [t]) 
let unboxRef t          = mkApp("BoxRef_proj_0", Arrow(Term_sort, Ref_sort), [t]) 
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

let mk_PreKind t      = mkApp("PreKind", Arrow(Type_sort, Kind_sort), [ t ]) 
let mk_PreType t      = mkApp("PreType", Arrow(Term_sort, Type_sort), [ t ]) 
let mk_Valid t        = mkApp("Valid", Arrow(Type_sort, Bool_sort), [ t ])  
let mk_HasType v t    = mkApp("HasType", Arrow(Term_sort, Arrow(Type_sort, Bool_sort)), [v;t])
let mk_HasKind t k    = mkApp("HasKind", Arrow(Type_sort, Arrow(Kind_sort, Bool_sort)), [t;k])
let mk_tester s n t   = mkApp("is_"^n, Arrow(s, Bool_sort), [t])
let mk_ApplyTE t e    = mkApp("ApplyTE", Arrow(Type_sort, Arrow(Term_sort, Type_sort)), [t;e])
let mk_ApplyTT t t'   = mkApp("ApplyTT", Arrow(Type_sort, Arrow(Type_sort, Type_sort)), [t;t'])
let mk_ApplyET e t    = mkApp("ApplyET", Arrow(Term_sort, Arrow(Type_sort, Term_sort)), [e;t])
let mk_ApplyEE e e'   = mkApp("ApplyEE", Arrow(Term_sort, Arrow(Term_sort, Term_sort)), [e;e'])
let mk_String_const i = mkApp("String_const", Arrow(Int_sort, String_sort), [ mkInteger i ])

let mk_and_opt p1 p2 = match p1, p2  with
  | Some p1, Some p2 -> Some (mkAnd(p1, p2))
  | Some p, None
  | None, Some p -> Some p
  | None, None -> None
    
let mk_and_opt_l pl = 
  List.fold_left (fun out p -> mk_and_opt p out) None pl 
    
let mk_and_l l = match l with 
  | [] -> []
  | hd::tl -> [List.fold_left (fun p1 p2 -> mkAnd(p1,p2)) hd tl]
