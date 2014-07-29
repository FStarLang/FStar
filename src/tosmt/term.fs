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

type caption = string
type var = int
type withsort<'a> = {tm:'a; tmsort:sort}

type term =
  | True
  | False
  | Funsym     of string
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
  | IfThenElse of term * term * term 
  | Forall     of list<pat> * list<(string * sort)> * term 
  | Exists     of list<pat> * list<(string * sort)> * term 
  | Select     of term * term 
  | Update     of term * term * term
  | ConstArray of string * sort * term 
  | Cases      of list<term>
  | Function   of int * (string * sort) * term
and pat = term

type binders = list<(string * sort)>
let rec fold_term (f:binders -> 'b -> term -> 'b) binders (b:'b) (t:term) : 'b = 
  let b = f binders b t in 
  match t with 
    | Funsym _
    | True
    | False
    | Integer _
    | BoundV _
    | FreeV _ -> b
    | App(_, _, tms) -> List.fold_left (fold_term f binders) b tms
    | ConstArray(_,_,t) 
    | Minus t
    | Not t -> fold_term f binders b t
    | PP(t1, t2) 
    | And(t1, t2)
    | Or(t1, t2)
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
    | Mod(t1, t2) 
    | Select(t1, t2) -> List.fold_left (fold_term f binders) b [t1;t2]
    | IfThenElse(t1, t2, t3) 
    | Update(t1, t2, t3) -> List.fold_left (fold_term f binders) b [t1;t2;t3]
    | Forall(pats, binders', body) 
    | Exists(pats, binders', body) -> 
      let binders = binders@binders' in 
      List.fold_left (fold_term f binders) b (pats@[body])
    | Cases tms -> 
      List.fold_left (fold_term f binders) b tms      
    | Function(_, sort, body) -> 
      fold_term f (binders@[sort]) b body

let free_bvars t = 
  let folder binders (bvars:list<(int * term)>) t = match t with 
    | BoundV(i, _, _) -> 
      let level = i - List.length binders in 
      if level >= 0 && not (Util.for_some (fun (l', _) -> l'=level) bvars)
      then (level, t)::bvars
      else bvars
    | _ -> bvars in 
  fold_term folder [] [] t

type typenames = list<string>
type projector = (string * sort)
type datacon   = (string * list<projector> * sort)
type datacons  = list<datacon>
type decl =
  | DefPrelude of typenames * datacons
  | DeclFun    of string * list<sort> * sort * option<caption>
  | DefineFun  of string * list<(string * sort)> * sort * term * option<caption>
  | Assume     of term   * option<caption>
  | Comment    of caption
  | Eval       of term
  | Echo       of string
type decls = list<decl>

let rec termEq (x:term) (y:term) =
  match x, y with 
    | PP(a, _), _ -> termEq a y
    | _, PP(b, _) -> termEq x b
    | Funsym s, Funsym t -> s=t
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
    | IfThenElse(t1, t2, t3), IfThenElse(s1, s2, s3) ->
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
    | Function(x, _, t1), Function(y,_,t2) -> termEq t1 t2 && x=y
    | _ -> false

let incrBoundV increment tm = 
  let rec aux ix tm = match tm with 
    | True
    | False
    | Integer _ 
    | FreeV _ -> tm
    | BoundV(i,s,xopt) -> 
      if i >= ix then BoundV(i+increment, s, xopt) else tm
    | App(s,sort, tms) -> App(s, sort, List.map (aux ix) tms)
    | Minus tm -> Minus (aux ix tm)
    | Not tm -> Not (aux ix tm)
    | PP(a,p) -> PP(aux ix a, aux ix p)
    | And(t1,t2) -> And(aux ix t1, aux ix t2)
    | Or(t1,t2) -> Or(aux ix t1, aux ix t2)
    | Imp(t1,t2) -> Imp(aux ix t1, aux ix t2)
    | Iff(t1,t2) -> Iff(aux ix t1, aux ix t2)
    | Eq(t1,t2) -> Eq(aux ix t1, aux ix t2)
    | LT(t1,t2) -> LT(aux ix t1, aux ix t2)
    | GT(t1,t2) -> GT(aux ix t1, aux ix t2)
    | LTE(t1,t2) -> LTE(aux ix t1, aux ix t2)
    | GTE(t1,t2) -> GTE(aux ix t1, aux ix t2)
    | Add(t1,t2) -> Add(aux ix t1, aux ix t2)
    | Sub(t1,t2) -> Sub(aux ix t1, aux ix t2)
    | Mul(t1,t2) -> Mul(aux ix t1, aux ix t2)
    | Div(t1,t2) -> Div(aux ix t1, aux ix t2)
    | Mod(t1,t2) -> Mod(aux ix t1, aux ix t2)
    | Select(t1, t2) -> Select(aux ix t1, aux ix t2) 
    | Update(t1, t2, t3) -> Update(aux ix t1, aux ix t2, aux ix t3)
    | IfThenElse(t1, t2, t3) ->  
        IfThenElse(aux ix t1, aux ix t2, aux ix t3)
    | Forall(pats, binders, tm) ->
        let ix = ix + List.length binders in 
          Forall(List.map (aux ix) pats, binders, aux ix tm)
    | Exists(pats, binders, tm) ->
        let ix = ix + List.length binders in 
          Exists(List.map (aux ix) pats, binders, aux ix tm)
    | ConstArray(s, t, tm) -> ConstArray(s, t, aux ix tm)
    | Cases tl -> Cases (List.map (aux ix) tl)
    | Function(x,s,tm) -> Function(x, s, aux ix tm)
  in aux 0 tm

let flatten_forall fa =  
  let rec aux (binders, pats) = fun tm -> match tm with 
    | Imp(guard, Forall(pats', binders', body)) -> 
        let guard = incrBoundV (List.length binders') guard in 
          aux (binders'@binders, pats'@pats) (Imp(guard, body))
    | Forall (pats', binders', body) -> 
        aux (binders'@binders, pats'@pats) body
    | _ -> 
        Forall(List.rev pats, List.rev binders, tm) in
    aux ([],[]) fa

let flatten_exists ex = 
  let rec aux (binders, pats) = fun tm -> match tm with
    | Exists (pats', binders', body) -> 
        aux (binders'@binders, pats'@pats) body
    | _ -> 
        Exists(List.rev pats, List.rev binders, tm) in
    aux ([],[]) ex  

let flatten_imp tm = 
  let mkAnd terms = match terms with 
    | [] -> raise Impos
    | hd::tl ->  List.fold_left (fun out term -> And(out, term)) hd tl in
  let rec aux out = fun tm -> match tm with
    | Imp(x, y) -> aux (x::out) y
    | _ -> Imp(mkAnd (List.rev out), tm) in
    aux [] tm

let flatten_arrow = fun q -> match q with 
  | Forall _ -> flatten_forall q
  | Exists _ -> flatten_exists q
  | Imp _ -> flatten_imp q
  | _ -> q
      
let flatten_and tm =
  let rec aux out = fun tm -> match tm with 
    | And(x, y) -> 
        let out = aux out x in 
          aux out y
    | _ -> tm::out in
    List.rev (aux [] tm)
      
let flatten_or tm = 
  let rec aux out = fun tm -> match tm with 
    | Or(x, y) -> 
        let out = aux out x in 
          aux out y
    | _ -> tm::out in
    List.rev (aux [] tm)


(*****************************************************)
(* Pretty printing terms and decls in SMT Lib format *)
(*****************************************************)
let string_of_either_bvd = function
  | Inl x -> Print.strBvd x
  | Inr x -> Print.strBvd x

let rec termToSmt binders tm = 
  let tm = flatten_arrow tm in
     match tm with
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
      | And(x,y) -> 
        format1 "(and %s)" (String.concat "\n" (List.map (termToSmt binders) (flatten_and tm)))
      | Or(x,y) -> 
        format1 "(or %s)" (String.concat "\n" (List.map (termToSmt binders) (flatten_or tm)))
      | Imp(x,y) -> 
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
      | IfThenElse(t1, t2, t3) -> 
        format3 "(ite %s %s %s)" (termToSmt binders t1) (termToSmt binders t2) (termToSmt binders t3)
      | Cases tms -> 
        format1 "(and %s)" (String.concat " " (List.map (termToSmt binders) tms))
      | Forall(pats,binders',z)
      | Exists(pats,binders',z) -> 
        let patsToSmt binders = function 
          | [] -> ""
          | pats -> format1 "\n:pattern (%s)" (String.concat " " (List.map (fun p -> format1 "%s" (termToSmt binders p)) pats)) in
        let strQuant = function 
          | Forall _ -> "forall"
          | Exists _ -> "exists" 
          | _ -> raise Impos in
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
      | _ -> 
        failwith "Unexpected term form" 

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
  | Comment(c) -> 
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

let mk_Kind_type        = App("Kind_type", Kind_sort, [])
let mk_Typ_const n      = App("Typ_const", Arrow(Ext "Type_name", Type_sort), [App(n, Ext "Type_name", [])])
let mk_Typ_app t1 t2    = App("Typ_app", Arrow(Type_sort, Arrow(Type_sort, Type_sort)), [t1;t2])
let mk_Typ_dep t1 t2    = App("Typ_dep", Arrow(Type_sort, Arrow(Term_sort, Type_sort)), [t1;t2])

let mk_Term_unit        = App("Term_unit", Term_sort, [])
let boxInt t            = App("BoxInt", Arrow(Int_sort, Term_sort), [t]) 
let unboxInt t          = App("BoxInt_proj_0", Arrow(Term_sort, Int_sort), [t]) 
let boxBool t           = App("BoxBool", Arrow(Bool_sort, Term_sort), [t]) 
let unboxBool t         = App("BoxBool_proj_0", Arrow(Term_sort, Bool_sort), [t]) 
let boxString t         = App("BoxString", Arrow(String_sort, Term_sort), [t]) 
let unboxString t       = App("BoxString_proj_0", Arrow(Term_sort, String_sort), [t]) 
let boxRef t            = App("BoxRef", Arrow(Ref_sort, Term_sort), [t]) 
let unboxRef t          = App("BoxRef_proj_0", Arrow(Term_sort, Ref_sort), [t]) 
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

let mk_PreKind t  = App("PreKind", Arrow(Type_sort, Kind_sort), [ t ]) 
let mk_PreType t  = App("PreType", Arrow(Term_sort, Type_sort), [ t ]) 
let mk_Valid t    = App("Valid", Arrow(Type_sort, Bool_sort), [ t ])  
let mk_String_const i = App("String_const", Arrow(Int_sort, String_sort), [ Integer i ])
let mk_HasType v t = App("HasType", Arrow(Term_sort, Arrow(Type_sort, Bool_sort)), [v;t])
let mk_HasKind t k = App("HasKind", Arrow(Type_sort, Arrow(Kind_sort, Bool_sort)), [t;k])
let mk_tester s n t = App("is_"^n, Arrow(s, Bool_sort), [t])
let mk_ApplyTE t e  = App("ApplyTE", Arrow(Type_sort, Arrow(Term_sort, Type_sort)), [t;e])
let mk_ApplyTT t t' = App("ApplyTT", Arrow(Type_sort, Arrow(Type_sort, Type_sort)), [t;t'])
let mk_ApplyET e t =  App("ApplyET", Arrow(Term_sort, Arrow(Type_sort, Term_sort)), [e;t])
let mk_ApplyEE e e' = App("ApplyEE", Arrow(Term_sort, Arrow(Term_sort, Term_sort)), [e;e'])

let mk_and_opt p1 p2 = match p1, p2  with
  | Some p1, Some p2 -> Some (And(p1, p2))
  | Some p, None
  | None, Some p -> Some p
  | None, None -> None
    
let mk_and_opt_l pl = 
  List.fold_left (fun out p -> mk_and_opt p out) None pl 
    
let mk_and_l l = match l with 
  | [] -> []
  | hd::tl -> [List.fold_left (fun p1 p2 -> And(p1,p2)) hd tl]

//let typeOf_tm_t =
//  let bool_t = mk_Typ_const (typeNameOfLid Const.bool_lid) in
//  let int_t = mk_Typ_const (typeNameOfLid Const.int_lid) in
//  let string_t = mk_Typ_const (typeNameOfLid Const.string_lid) in
//  let heap_t = mk_Typ_const (typeNameOfLid Const.heap_lid) in
//  let ref_t = mk_Typ_const (typeNameOfLid Const.ref_lid) in
//  let unit_t = mk_Typ_const (typeNameOfLid Const.unit_lid) in
//  fun tm t -> 
//    let eqt = Eq(typeOf tm, t) in 
//    if termEq t bool_t 
//    then And(eqt, App(mkTester "BoxBool", Arrow(Term_sort, Bool_sort), [tm]))
//    else if termEq t int_t
//    then And(eqt, App(mkTester "BoxInt", Arrow(Term_sort, Bool_sort), [tm]))
//    else if termEq t string_t 
//    then And(eqt, App(mkTester "BoxString", Arrow(Term_sort, Bool_sort), [tm]))
//    else if termEq t unit_t 
//    then And(eqt, Eq(tm, unitTerm))
//    else match t.tm with 
//      | App("Typ_app", _, [s; tt]) -> 
//        if termEq s ref_t 
//        then And(eqt, 
//                 And(App(mkTester "BoxRef", Arrow(Term_sort, Bool_sort), [|tm|]), 
//                     Eq(kindOf tt, mk_Kind_star())))
//        else eqt
//      | _ -> eqt
//        
//let kindOf_t_k t k = Eq(kindOf t, k)
