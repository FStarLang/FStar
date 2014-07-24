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

let ssl (sl:string list) : string = String.concat "." sl
let string_of_bvd bvd = bvd.realname.idText

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
  
let rec strSort = function
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

type assumptionId =
  | ABindingVar    of int
  | ABindingMatch  of int
  | AName          of string

let strOfAssumptionId = function
  | ABindingVar i     -> format1 "ABindingVar %s" <| string_of_int i
  | ABindingMatch i   -> format1 "ABindingMatch %s" <| string_of_int i
  | AName s           -> s

type caption = string
type var = int
type withsort<'a> = {tm:'a; tmsort:sort}

type term' =
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
  | IfThenElse of term * term * term * option<term>
  | Forall     of list<pat> * list<sort> * list<(either<btvdef,bvvdef> * termref)> * term 
  | Exists     of list<pat> * list<sort> * list<(either<btvdef,bvvdef> * termref)> * term 
  | Select     of term * term 
  | Update     of term * term * term
  | ConstArray of string * sort * term 
  | Cases      of list<term>
  | Function   of int * sort * term
and term   = withsort<term'>
and termref = ref<option<term>>
and pat = term

type binders = sort list
let rec fold_term (f:binders -> 'b -> term -> 'b) binders (b:'b) (t:term) : 'b = 
  let b = f binders b t in 
  match t.tm with 
    | Funsym _
    | True _
    | False _
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
    | IfThenElse(t1, t2, t3, None) 
    | Update(t1, t2, t3) -> List.fold_left (fold_term f binders) b [t1;t2;t3]
    | Forall(pats, binders', _, body) 
    | Exists(pats, binders', _, body) -> 
      let binders = binders@binders' in 
      List.fold_left (fold_term f binders) b (pats@[body])
    | Cases tms -> 
      List.fold_left (fold_term f binders) b tms      
    | Function(_, sort, body) -> 
      fold_term f (binders@[sort]) b body

let free_bvars t = 
  let folder binders (bvars:list<(int * term)>) t = match t.tm with 
    | BoundV(i, _, _) -> 
      let level = i - List.length binders in 
      if level >= 0 && not (List.exists (fun (l', _) -> l'=level) bvars)
      then (level, t)::bvars
      else bvars
    | _ -> bvars in 
  fold_term folder [] [] t

let termref () = ref None
let asBool tm = {tm=tm; tmsort=Bool_sort}
let asInt tm = {tm=tm; tmsort=Int_sort}
let asType tm = {tm=tm; tmsort=Type_sort}
let asTerm tm = {tm=tm; tmsort=Term_sort}
let withSort s tm = {tm=tm; tmsort=s}
let asKind tm = {tm=tm; tmsort=Kind_sort}

let mkBoundV (i,j,x) = withSort j <| BoundV(i,j,x)
let mkTrue = asBool True
let mkFalse = asBool False
let mkInteger i = asInt <| Integer i
let mkPP (a,p) = withSort a.tmsort <| PP(a,p)
let mkFreeV (n,s) = withSort s <| FreeV(n,s)
let mkNot t = asBool <| Not t
let mkFunction(x,s,t) = withSort (Arrow(s,t.tmsort)) <| Function(x,s,t)
let arrowSort result tms = List.fold_right (fun tm out -> Arrow(tm.tmsort, out)) tms result

#if CHECKED
let And(t1,t2) = 
  if t1.tmsort<>Bool_sort || t2.tmsort<>Bool_sort 
  then raise (Bad(spr "Expected bool sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asBool <| And(t1,t2)

let Or(t1,t2) = 
  if t1.tmsort<>Bool_sort || t2.tmsort<>Bool_sort 
  then raise (Bad(spr "Expected bool sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asBool <| Or(t1,t2) 
let Imp(t1,t2) = 
  if t1.tmsort<>Bool_sort || t2.tmsort<>Bool_sort 
  then raise (Bad(spr "Expected bool sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asBool <| Imp(t1,t2)
let Iff(t1,t2) =   
  if t1.tmsort<>Bool_sort || t2.tmsort<>Bool_sort 
  then raise (Bad(spr "Expected bool sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asBool <| Iff(t1,t2) 
let Eq(t1,t2) = 
  if t1.tmsort<>t2.tmsort
  then raise (Bad(spr "Expected equal sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asBool <| Eq(t1,t2)
let LT(t1,t2) = 
  if t1.tmsort<>Int_sort || t2.tmsort<>Int_sort 
  then raise (Bad(spr "Expected int sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asBool <| LT(t1,t2)
let LTE(t1,t2) = 
  if t1.tmsort<>Int_sort || t2.tmsort<>Int_sort 
  then raise (Bad(spr "Expected int sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asBool <| LTE(t1,t2)
let GT(t1,t2) = 
  if t1.tmsort<>Int_sort || t2.tmsort<>Int_sort 
  then raise (Bad(spr "Expected int sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asBool <| GT(t1,t2)
let GTE(t1,t2) = 
  if t1.tmsort<>Int_sort || t2.tmsort<>Int_sort 
  then raise (Bad(spr "Expected int sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asBool <| GTE(t1,t2)
let Minus(t1) = 
  if t1.tmsort<>Int_sort
  then raise (Bad(spr "Expected int sorts; got %A" t1.tmsort))
  else asInt <| Minus(t1)
let Add(t1,t2) = 
  if t1.tmsort<>Int_sort || t2.tmsort<>Int_sort 
  then raise (Bad(spr "Expected int sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asInt <| Add(t1,t2)
let Sub(t1,t2) = 
  if t1.tmsort<>Int_sort || t2.tmsort<>Int_sort 
  then raise (Bad(spr "Expected int sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asInt <| Sub(t1,t2)
let Mul(t1,t2) = 
  if t1.tmsort<>Int_sort || t2.tmsort<>Int_sort 
  then raise (Bad(spr "Expected int sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asInt <| Mul(t1,t2)
let Div(t1,t2) = 
  if t1.tmsort<>Int_sort || t2.tmsort<>Int_sort 
  then raise (Bad(spr "Expected int sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asInt <| Div(t1,t2)
let Mod(t1,t2) = 
  if t1.tmsort<>Int_sort || t2.tmsort<>Int_sort 
  then raise (Bad(spr "Expected int sorts; got %A,%A" t1.tmsort t2.tmsort))
  else asInt <| Mod(t1,t2)
let IfThenElse(t1,t2,t3,t4) = 
  if t1.tmsort<>Bool_sort || (t2.tmsort <> t3.tmsort) 
  then raise (Bad(spr "Expected int sorts; got %A,%A" t1.tmsort t2.tmsort))
  else withSort t3.tmsort <| IfThenElse(t1,t2,t3,t4)
let Forall(p,s,x,t) = 
  if t.tmsort <> Bool_sort
  then raise (Bad(spr "Expected bool sort; got %A" t.tmsort))
  else asBool <| Forall(p,s,x,t)
let Exists(p,s,x,t) = 
  if t.tmsort <> Bool_sort
  then raise (Bad(spr "Expected bool sort; got %A" t.tmsort))
  else asBool <| Exists(p,s,x,t)
let Update(t1,t2,t3) = 
  match t1.tmsort with
    | Array(s1,s2) when t2.tmsort=s1 && t3.tmsort=s2 -> 
        withSort t1.tmsort <| Update(t1,t2,t3)
    | _ -> raise (Bad(spr "Ill-sorted update term: %A, %A, %A" t1.tmsort t2.tmsort t3.tmsort))
let ConstArray(n,s,t) = withSort (Array(s,t.tmsort)) <| ConstArray(n,s,t)
let Cases tl = 
  List.iter (fun t -> if t.tmsort <> Bool_sort then raise (Bad (spr "Expected Bool_sort in cases; got %A;\n %s\n" t.tmsort (t.ToString()))) else ()) tl;
  asBool <| Cases tl

let Application(t1,t2) = match t1.tmsort with
    | Arrow(s1, s2) when s1=t2.tmsort -> withSort s2 <| Application(t1,t2)
    | _ -> raise (Bad(spr "Expected sort Arrow(%A,_) got %A" t2.tmsort t1.tmsort))
let Appl(f,s,tms) = 
  let sort  = tms |> List.fold_left (fun out {tmsort=s} -> match out with 
                        | Arrow(s1, out) when s1=s -> out
                        | _ -> raise (Bad(spr "Expected sort Arrow(%A, _); got %A" s out))) s  in
    withSort sort <| App(f,s,tms)
let App(f,s,tms) =
   let sort  = tm) |> List.fold_left (fun out {tmsort=s} -> match out with 
                        | Arrow(s1, out) when s1=s -> out
                        | _ -> raise (Bad(spr "Expected sort Arrow(%A, _); got %A" s out))) s  in
    withSort sort <| App(f,s,tms)
let Select(t1,t2) = match t1.tmsort with 
    | Array(s1,s2) when s1=t2.tmsort -> withSort s2 <| Select(t1,t2)
    | _ -> raise (Bad(spr "Expected sort Arrary(%A, _); got %A" t2.tmsort t1.tmsort))
#else
let unsort = Ext "Un"
let withSort' x = withSort unsort x
let mkAnd(t1,t2) = withSort' <| And(t1,t2)
let mkOr(t1,t2) =  withSort' <| Or(t1,t2) 
let mkImp(t1,t2) = withSort' <| Imp(t1,t2)
let mkIff(t1,t2) = withSort' <| Iff(t1,t2) 
let mkEq(t1,t2) = withSort' <| Eq(t1,t2)
let mkLT(t1,t2) = withSort' <| LT(t1,t2)
let mkLTE(t1,t2) = withSort' <| LTE(t1,t2)
let mkGT(t1,t2) =  withSort' <| GT(t1,t2)
let mkGTE(t1,t2) = withSort' <| GTE(t1,t2)
let mkMinus(t1) = withSort' <| Minus(t1)
let mkAdd(t1,t2) = withSort' <| Add(t1,t2)
let mkSub(t1,t2) = withSort' <| Sub(t1,t2)
let mkMul(t1,t2) = withSort' <| Mul(t1,t2)
let mkDiv(t1,t2) = withSort' <| Div(t1,t2)
let mkMod(t1,t2) = withSort' <| Mod(t1,t2)
let mkIfThenElse(t1,t2,t3,t4) = withSort' <| IfThenElse(t1,t2,t3,t4)
let mkForall(p,s,x,t) = withSort' <| Forall(p,s,x,t)
let mkExists(p,s,x,t) = withSort' <| Exists(p,s,x,t)
let mkUpdate(t1,t2,t3) = withSort' <| Update(t1,t2,t3)
let mkConstArray(n,s,t) = withSort' <| ConstArray(n,s,t)
let mkCases tl = withSort' <| Cases tl
let mkApp(f,s,tms) = withSort' <| App(f,s,tms)
let mkSelect(t1,t2) = withSort' <| Select(t1,t2)
#endif

type constr = {cname:string;
               tester:string;
               projectors:list<string>;
               sorts:list<either<sort, string>>;
               recindexes:list<uint32>}
type decl =
  | DefPrelude of string
  | DefData    of list<(string * list<constr>)>
  | DefSort    of sort   * option<caption>
  | DefPred    of string * list<sort> * option<caption>
  | DeclFun    of string * list<sort> * sort * option<caption>
  | DefineFun  of string * list<(string * sort)> * sort * term * option<caption>
  | Assume     of term   * option<caption> * assumptionId
  | Query      of term
  | Comment    of caption
  | Echo       of string
  | Eval       of term
type decls = list<decl>

let rec termEq (x:term) (y:term) =
  match x.tm, y.tm with 
    | PP(a, _), _ -> termEq a y
    | _, PP(b, _) -> termEq x b
    | Funsym s, Funsym t -> s=t
    | True, True
    | False, False -> true
    | Integer i, Integer j -> i=j
    | BoundV(i, s, _), BoundV(j, t, _) -> i=j  && s=t
    | FreeV(x,s), FreeV(y,t) -> x=y && s=t
    | App(f,_,tl), App(g,_,sl) when tl.Length=sl.Length ->
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
    | IfThenElse(t1, t2, t3, _), IfThenElse(s1, s2, s3, _) ->
        termEq t1 (s1) && termEq t2 (s2) && termEq t3 (s3)
    | Forall(pl, sorts, _, t), Forall(ql, sorts', _, s) 
    | Exists(pl, sorts, _, t), Forall(ql, sorts', _, s) -> 
        (List.forall2 termEq pl ql) &&
          sorts=sorts' &&
        termEq t (s)
    | ConstArray(str, sort, t), ConstArray(str', sort', s) -> 
        termEq t (s) && str=str' && sort=sort'
    | Cases(tl), Cases(sl) when tl.Length=sl.Length -> 
        List.forall2 termEq tl sl
    | Function(x, _, t1), Function(y,_,t2) -> termEq t1 t2 && x=y
    | _ -> false


let incrBoundV increment tm = 
  let rec aux ix tm = match tm.tm with 
    | True
    | False
    | Integer _ 
    | FreeV _ -> tm
    | BoundV(i,s,xopt) -> 
      if i >= ix then mkBoundV(i+increment, s, xopt) else tm
    | App(s,sort, tms) -> mkApp(s, sort, List.map (aux ix) tms)
    | Minus tm -> mkMinus (aux ix tm)
    | Not tm -> mkNot (aux ix tm)
    | PP(a,p) -> mkPP(aux ix a, aux ix p)
    | And(t1,t2) -> mkAnd(aux ix t1, aux ix t2)
    | Or(t1,t2) -> mkOr(aux ix t1, aux ix t2)
    | Imp(t1,t2) -> mkImp(aux ix t1, aux ix t2)
    | Iff(t1,t2) -> mkIff(aux ix t1, aux ix t2)
    | Eq(t1,t2) -> mkEq(aux ix t1, aux ix t2)
    | LT(t1,t2) -> mkLT(aux ix t1, aux ix t2)
    | GT(t1,t2) -> mkGT(aux ix t1, aux ix t2)
    | LTE(t1,t2) -> mkLTE(aux ix t1, aux ix t2)
    | GTE(t1,t2) -> mkGTE(aux ix t1, aux ix t2)
    | Add(t1,t2) -> mkAdd(aux ix t1, aux ix t2)
    | Sub(t1,t2) -> mkSub(aux ix t1, aux ix t2)
    | Mul(t1,t2) -> mkMul(aux ix t1, aux ix t2)
    | Div(t1,t2) -> mkDiv(aux ix t1, aux ix t2)
    | Mod(t1,t2) -> mkMod(aux ix t1, aux ix t2)
    | Select(t1, t2) -> mkSelect(aux ix t1, aux ix t2) 
    | Update(t1, t2, t3) -> mkUpdate(aux ix t1, aux ix t2, aux ix t3)
    | IfThenElse(t1, t2, t3, None) ->  
        mkIfThenElse(aux ix t1, aux ix t2, aux ix t3, None)
    | IfThenElse(t1, t2, t3, Some t4) ->  
        mkIfThenElse(aux ix t1, aux ix t2, aux ix t3, Some (aux ix t4))
    | Forall(pats, sorts, names, tm) ->
        let ix = ix + List.length sorts in 
          mkForall(List.map (aux ix) pats, sorts, names, aux ix tm)
    | Exists(pats, sorts, names, tm) ->
        let ix = ix + List.length sorts in 
          mkExists(List.map (aux ix) pats, sorts, names, aux ix tm)
    | ConstArray(s, t, tm) -> mkConstArray(s, t, aux ix tm)
    | Cases tl -> mkCases (List.map (aux ix) tl)
    | Function(x,s,tm) -> mkFunction(x, s, aux ix tm)
  in aux 0 tm

let flatten_forall fa =  
  let rec aux (binders, pats) = fun tm -> match tm.tm with 
    | Imp(guard, {tm=Forall(pats', sorts, names, body)}) -> 
        let guard = incrBoundV (sorts.Length) guard in 
          aux ((sorts, names)::binders, pats'@pats) (mkImp(guard, body))
    | Forall (pats', sorts, names, body) -> 
        aux ((sorts, names)::binders, pats'@pats) body
    | _ -> 
        let sorts, names = List.unzip (List.rev binders) in
        let pats = List.rev pats in
          mkForall(pats, List.concat sorts, List.concat names, tm) in
    aux ([],[]) fa

let flatten_exists ex = 
  let rec aux (binders, pats) = fun tm -> match tm.tm with
    | Exists (pats', sorts, names, body) -> 
        aux ((sorts, names)::binders, pats'@pats) body
    | _ -> 
        let sorts, names = List.unzip (List.rev binders) in
        let pats = List.rev pats in
          mkExists(pats, List.concat sorts, List.concat names, tm) in
    aux ([],[]) ex  

let flatten_imp tm = 
  let mkAnd terms = match terms with 
    | [] -> raise Impos
    | hd::tl ->  List.fold_left (fun out term -> mkAnd(out, term)) hd tl in
  let rec aux out = fun tm -> match tm.tm with
    | Imp(x, y) -> aux (x::out) y
    | _ -> mkImp(mkAnd (List.rev out), tm) in
    aux [] tm

let flatten_arrow = fun q -> match q.tm with 
  | Forall _ -> flatten_forall q
  | Exists _ -> flatten_exists q
  | Imp _ -> flatten_imp q
  | _ -> q
      
let flatten_and tm =
  let rec aux out = fun tm -> match tm.tm with 
    | And(x, y) -> 
        let out = aux out x in 
          aux out y
    | _ -> tm::out in
    List.rev (aux [] tm)
      
let flatten_or tm = 
  let rec aux out = fun tm -> match tm.tm with 
    | Or(x, y) -> 
        let out = aux out x in 
          aux out y
    | _ -> tm::out in
    List.rev (aux [] tm)


(*****************************************************)
(* Pretty printing terms and decls in SMT Lib format *)
(*****************************************************)
type info          = { binders: list<either<btvdef,bvvdef>>; pp_name_map:smap<string>}
let init_info z3 m = { binders = []; pp_name_map=m }

let map_pp info f = 
  if !Options.print_real_names 
  then f
  else match Util.smap_try_find info.pp_name_map f with 
    | Some g -> g
    | _ -> f 

let string_of_either_bvd = function
  | Inl x -> Print.strBvd x
  | Inr x -> Print.strBvd x

let rec termToSmt (info:info) tm = 
  let tm = flatten_arrow tm in
  match tm.tm with
  | True          -> "true"
  | False         -> "false"
  | Integer i     -> 
    if i < 0 then Util.format1 "(- %d)" (string_of_int -i) 
    else string_of_int i
  | PP(_,q) -> 
    termToSmt info q
  | BoundV(i,_,_) as tm  -> 
    if (i < List.length info.binders) 
    then string_of_either_bvd (List.nth info.binders i)
    else failwith "Bad index for bound variable in formula" 
  | FreeV(x,_)    -> map_pp info x 
  | App(f,_,es) when (es.Length=0) -> map_pp info f
  | App(f,_, es)     -> 
    let f = map_pp info f in
    let a = List.map (termToSmt info) es in
    let s = String.concat " " a in
    format2 "(%s %s)" f s
  | Not(x) -> 
    format1 "(not %s)" (termToSmt info x)
  | And(x,y) -> 
    format1 "(and %s)" (String.concat "\n" (List.map (termToSmt info) (flatten_and tm)))
  | Or(x,y) -> 
    format1 "(or %s)" (String.concat "\n" (List.map (termToSmt info) (flatten_or tm)))
  | Imp(x,y) -> 
    format2 "(implies %s\n %s)"(termToSmt info x)(termToSmt info y)
  | Iff(x,y) -> 
    format2 "(iff %s\n %s)" (termToSmt info x) (termToSmt info y)
  | Eq(x,y) -> 
    format2 "(= %s\n %s)" (termToSmt info x) (termToSmt info y)
  | LT(x,y) -> 
    format2 "(< %s %s)" (termToSmt info x) (termToSmt info y)
  | GT(x,y) -> 
    format2 "(> %s %s)" (termToSmt info x) (termToSmt info y)
  | LTE(x,y) -> 
    format2 "(<= %s %s)" (termToSmt info x) (termToSmt info y)
  | GTE(x,y) -> 
    format2 "(>= %s %s)" (termToSmt info x) (termToSmt info y)
  | Minus(t1) -> 
    format1 "(- %s)" (termToSmt info t1)
  | Add(t1,t2) -> 
    format2 "(+ %s\n %s)" (termToSmt info t1) (termToSmt info t2)
  | Sub(t1,t2) -> 
    format2 "(- %s\n %s)" (termToSmt info t1) (termToSmt info t2)
  | Mul(t1,t2) -> 
    format2 "(* %s\n %s)" (termToSmt info t1) (termToSmt info t2)
  | Div(t1,t2) -> 
    format2 "(div %s\n %s)" (termToSmt info t1) (termToSmt info t2)
  | Mod(t1,t2) -> 
    format2 "(mod %s\n %s)" (termToSmt info t1) (termToSmt info t2)
  | Select(h,l) -> 
    format2 "(select %s %s)" (termToSmt info h) (termToSmt info l)
  | Update(h,l,v) -> 
    format3 "(store %s %s %s)" (termToSmt info h) (termToSmt info l) (termToSmt info v)
  | IfThenElse(_, _, _, Some t4) -> 
    termToSmt info t4
  | IfThenElse(t1, t2, t3, _) -> 
    format3 "(ite %s %s %s)" (termToSmt info t1) (termToSmt info t2) (termToSmt info t3)
  | Cases tms -> 
    format1 "(and %s)" (String.concat " " (List.map (termToSmt info) tms))
  | Forall(pats,x,y,z)
  | Exists(pats,x,y,z) as q -> 
      if List.length x <> List.length y 
      then failwith "Unequal number of bound variables and their sorts"
      else
        let s = String.concat " "
          (List.map (fun (a,b) -> format2 "(%s %s)" (string_of_either_bvd <| fst a) (strSort b))
             (List.zip y x)) in
        let binders' = (List.rev (List.map fst y)) @ info.binders in
        let info' = { info with binders=binders' } in
          format3 "\n\n(%s (%s)\n\n %s)" (strQuant q) s
            (if pats.Length <> 0 
             then format2 "(! %s\n %s)" (termToSmt info' z) (patsToSmt info' pats)
             else termToSmt info' z)
  | ConstArray(s, _, tm) -> 
    format2 "((as const %s) %s)" s (termToSmt info tm)
  | _ -> 
    failwith "Unexpected term form"

and strQuant = function 
  | Forall _ -> "forall"
  | Exists _ -> "exists" 
  | _ -> raise Impos

and patsToSmt info  = function 
  | [] -> ""
  | pats -> format1 "\n:pattern (%s)" (String.concat " " (List.map (fun p -> format1 "%s" (termToSmt info p)) pats))
    
let strOfStrOpt = function Some x -> x | _ -> ""

let declToSmt info decl = match decl with
  | DefPrelude p -> p
  | DefSort(tiio, msg_opt) -> 
    format2 "\n(declare-sort %s) ; %s" (strSort tiio) (strOfStrOpt msg_opt)
  | Query(t) -> 
    format1 "\n(assert (not %s)) \n (check-sat)" (termToSmt info t)
  | Comment(c) -> 
    format1 "\n; %s" c
  | DefPred(f,sorts,_) ->
    let f = map_pp info f in 
    let l = List.map strSort sorts in
    format2 "\n(declare-fun %s (%s) Bool)" f (String.concat " " l)
  | DefData dts -> 
    format1 "(declare-datatypes () (%s))"
      (String.concat "\n" <|
         (dts |> List.map (fun (d, constrs) -> 
                     let constrs = constrs |> List.map 
                         (fun c -> 
                           let cargs = List.map2 
                            (fun pname sort -> match sort with 
                               | Inl s -> format2 "(%s %s)" pname (strSort s)
                               | Inr s -> format2 "(%s %s)" pname s)
                            c.projectors c.sorts in 
                           let cargs = String.concat " " cargs in 
                             format2 "(%s %s)" c.cname cargs) in
                       format2 "(%s %s)" d (String.concat "\n" constrs))))

  | DeclFun(f,argsorts,retsort,_) ->
    let f = map_pp info f in  
    let l = List.map strSort argsorts in
    format3 "(declare-fun %s (%s) %s)" f (String.concat " " l) (strSort retsort)
  | DefineFun(f,args,retsort,body,_) ->
    let f = map_pp info f in  
    let l = List.map (fun (nm,s) -> format2 "(%s %s)" nm (strSort s)) args in
    let info = args |> List.fold_left 
        (fun info (x,s) -> let x = mk_ident(x,dummyRange) in {info with binders=(Inl (Util.mkbvd (x,x)))::info.binders})
        info  in
    format4 "(define-fun %s (%s) %s\n %s)" f (String.concat " " l) (strSort retsort) (termToSmt info body)
  | Assume(t,co,aid) ->
    let s = strOfAssumptionId aid in
    let c = match co with 
      | Some c -> format2 ";;;;;;;;;;; %s (aid %s)\n" c s
      | None -> format1 ";;;;;;;;;;; (aid %s)\n" s in
    format2 "%s (assert %s)" c (termToSmt info t)
  | Echo s -> format1 "(echo \"%s\")" s
  | Eval t -> format1 "(eval %s)" (termToSmt info t)

(****************************************************************************)
(* Standard SMTLib prelude for F* and some term constructors                *)
(****************************************************************************)

let mkPrelude typenames termconstrs = 
 format2 "(declare-sort Ref)\n \
          (declare-datatypes () ((String (String_const (String_const_proj_0 Int))))) \n \
          (declare-datatypes () ((Type_name (Typ_name_other (Type_name_other_id Int)) \n \
                                             %s))) \n \
          (declare-datatypes () ((Kind (Kind_other (Kind_other_id Int)) \n \
                                       (Kind_type)) \n \
                                 (Type (Typ_other (Typ_other_id Int)) \n \
                                       (Typ_const (Typ_const_fst Type_name)) \n \
                                       (Typ_app (Typ_app_fst Type) (Typ_app_snd Type)) \n \
                                       (Typ_dep (Typ_dep_fst Type) (Typ_dep_snd Term))) \n \
                                 (Term (Term_other (Term_other_id Int)) \n \
                                       (Term_unit) \n \
                                       (BoxInt (BoxInt_proj_0 Int)) \n \
                                       (BoxBool (BoxBool_proj_0 Bool)) \n \
                                       (BoxString (BoxString_proj_0 String)) \n \
                                       (BoxRef (BoxRef_proj_0 Ref)) \n \
                                       %s)))\n \
          (declare-fun KindOf (Type) Kind)\n \
          (declare-fun TypeOf (Term) Type)\n \
          (declare-fun Valid (Type) Bool)\n \
          (declare-fun Eval (Term) Term)\n \
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
         typenames termconstrs

let mk_Kind_type        = App("Kind_type", Kind_sort, [])
let mk_Typ_const n      = App("Typ_const", Arrow(Ext "Type_name", Type_sort), [mkApp(n, Ext "Type_name", [])])
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

let kindOf t  = App("KindOf", Arrow(Type_sort, Kind_sort), [ t ]) 
let typeOf t  = App("TypeOf", Arrow(Term_sort, Type_sort), [ t ]) 
let eval t    = App("Eval", Arrow(Term_sort, Term_sort), [ t ]) 
let valid t   = App("Valid", Arrow(Type_sort, Bool_sort), [ t ])  
let mk_String_const i = App("String_const", Arrow(Int_sort, String_sort), [ mkInteger i ])

