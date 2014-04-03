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
(* 
   Copyright Microsoft Research. 2009-2013
*)
#light "off"

module Microsoft.FStar.Z3Encoding.Term

open System.Diagnostics
open Microsoft.Z3
type ZZZError = Microsoft.Z3.Z3Exception
open Microsoft.FStar
open Absyn
open Util
open Profiling 

let _ = Profiling.new_counter "Z3 query"
let _ = Profiling.new_counter "Z3 encoding"
let _ = Profiling.new_counter "Z3 term translation"
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
  | Pseudo_term_sort
  | Pseudo_term_opt_sort
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
  | Pseudo_term_sort -> "Pseudo_term"
  | Pseudo_term_opt_sort  -> "Pseudo_term_opt"
  | Array(s1, s2) -> spr "(Array %s %s)" (strSort s1) (strSort s2)
  | Arrow(s1, s2) -> spr "(%s -> %s)" (strSort s1) (strSort s2)
  | Ext s -> s

type assumptionId =
  | ABindingVar    of int
  | ABindingMatch  of int
  | AName          of string

let strOfAssumptionId = function
  | ABindingVar i     -> spr "ABindingVar %d" i
  | ABindingMatch i   -> spr "ABindingMatch %d" i
  | AName s           -> s

type caption = string

type var = int

type withsort<'a> = {tm:'a; tmsort:sort}
with override x.ToString() = spr "%s" (x.tm.ToString())
end

type 'a term' =
  | Hole     of var
  | Funsym   of string
  | True
  | False
  | Integer  of int
  | BoundV   of int * sort * string * termref<'a>
  | FreeV    of string * sort
  | PP       of term<'a> * term<'a>
  | App      of string * sort * term<'a> array 
  | Not      of term<'a>
  | And      of term<'a> * term<'a>
  | Or       of term<'a> * term<'a>
  | Imp      of term<'a> * term<'a>
  | Iff      of term<'a> * term<'a>
  | Eq       of term<'a> * term<'a>
  | LT       of term<'a> * term<'a>
  | LTE      of term<'a> * term<'a>
  | GT       of term<'a> * term<'a>
  | GTE      of term<'a> * term<'a>
  | Add      of term<'a> * term<'a>
  | Sub      of term<'a> * term<'a>
  | Div      of term<'a> * term<'a>
  | Mul      of term<'a> * term<'a>
  | Minus    of term<'a>
  | Mod      of term<'a> * term<'a>
  | IfThenElse of term<'a> * term<'a> * term<'a> * term<'a> option
  | Forall   of pat<'a> list * sort array * (Disj<btvdef,bvvdef> * termref<'a>) array * term<'a> 
  | Exists   of pat<'a> list * sort array * (Disj<btvdef,bvvdef> * termref<'a>) array * term<'a> 
  | Select   of term<'a> * term<'a> 
  | Update   of term<'a> * term<'a> * term<'a>
  | ConstArray of string * sort * term<'a> 
  | Z3Term   of Expr 
  | Cases    of term<'a> list
  | Residue  of (term<'a> * 'a)
  | ResFree  of term<'a>
  | Function    of (var * sort * term<'a>)
  | Application of (term<'a> * term<'a>)
and 'a term = withsort<'a term'>
and 'a termref = ref<option<'a term>>
and pat<'a> = term<'a>

type binders = sort list
let rec fold_term (f:binders -> 'b -> term<'a> -> 'b) binders (b:'b) (t:term<'a>) : 'b = 
  let b = f binders b t in 
  match t.tm with 
    | Z3Term _ -> b
    | Hole _
    | Funsym _
    | True _
    | False _
    | Integer _
    | BoundV _
    | FreeV _ -> b
    | App(_, _, tms) -> Array.fold (fold_term f binders) b tms
    | ResFree t
    | Residue(t, _)
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
    | Select(t1, t2)
    | Application(t1, t2) -> List.fold_left (fold_term f binders) b [t1;t2] 
    | IfThenElse(t1, t2, t3, None) 
    | Update(t1, t2, t3) -> List.fold_left (fold_term f binders) b [t1;t2;t3]
    | Forall(pats, binders', _, body) 
    | Exists(pats, binders', _, body) -> 
      let binders = binders@(List.ofArray binders') in 
      List.fold_left (fold_term f binders) b (pats@[body])
    | Cases tms -> 
      List.fold_left (fold_term f binders) b tms      
    | Function(_, sort, body) -> 
      fold_term f (binders@[sort]) b body

let free_bvars t = 
  let folder binders (bvars:list<int * term<'a>>) t = match t.tm with 
    | BoundV(i, _, _, _) -> 
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
(* let asHeap tm = {tm=tm; tmsort=Heap_sort} *)
let withSort s tm = {tm=tm; tmsort=s}
let asKind tm = {tm=tm; tmsort=Kind_sort}

let rec comp tm = match tm.tm with 
  | BoundV(_, _, _, r) -> (match !r with None -> tm | Some tm -> comp tm)
  | _ -> tm
and comp' tm = (comp (asBool tm)).tm

let BoundV (i,j,x,r) = withSort j <| BoundV(i,j,x,r)
let True () = asBool True
let False () = asBool False
let Integer i = asInt <| Integer i
let PP (a,p) = withSort a.tmsort <| PP(a,p)
let FreeV (n,s) = withSort s <| FreeV(n,s)
let Not t = asBool <| Not t
let Residue(tm,x) = asBool <| Residue(tm,x)
let ResFree(tm) = withSort tm.tmsort <| ResFree(tm)
let Function(x,s,t) = withSort (Arrow(s,t.tmsort)) <| Function(x,s,t)
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
    withSort sort <| App(f,s,Array.ofList tms)
let App(f,s,tms) =
   let sort  = (List.ofArray tms) |> List.fold_left (fun out {tmsort=s} -> match out with 
                        | Arrow(s1, out) when s1=s -> out
                        | _ -> raise (Bad(spr "Expected sort Arrow(%A, _); got %A" s out))) s  in
    withSort sort <| App(f,s,tms)
let Select(t1,t2) = match t1.tmsort with 
    | Array(s1,s2) when s1=t2.tmsort -> withSort s2 <| Select(t1,t2)
    | _ -> raise (Bad(spr "Expected sort Arrary(%A, _); got %A" t2.tmsort t1.tmsort))
#else
let unsort = Ext "Un"
let withSort' x = withSort unsort x
let And(t1,t2) = withSort' <| And(t1,t2)
let Or(t1,t2) =  withSort' <| Or(t1,t2) 
let Imp(t1,t2) = withSort' <| Imp(t1,t2)
let Iff(t1,t2) = withSort' <| Iff(t1,t2) 
let Eq(t1,t2) = withSort' <| Eq(t1,t2)
let LT(t1,t2) = withSort' <| LT(t1,t2)
let LTE(t1,t2) = withSort' <| LTE(t1,t2)
let GT(t1,t2) =  withSort' <| GT(t1,t2)
let GTE(t1,t2) = withSort' <| GTE(t1,t2)
let Minus(t1) = withSort' <| Minus(t1)
let Add(t1,t2) = withSort' <| Add(t1,t2)
let Sub(t1,t2) = withSort' <| Sub(t1,t2)
let Mul(t1,t2) = withSort' <| Mul(t1,t2)
let Div(t1,t2) = withSort' <| Div(t1,t2)
let Mod(t1,t2) = withSort' <| Mod(t1,t2)
let IfThenElse(t1,t2,t3,t4) = withSort' <| IfThenElse(t1,t2,t3,t4)
let Forall(p,s,x,t) = withSort' <| Forall(p,s,x,t)
let Exists(p,s,x,t) = withSort' <| Exists(p,s,x,t)
let Update(t1,t2,t3) = withSort' <| Update(t1,t2,t3)
let ConstArray(n,s,t) = withSort' <| ConstArray(n,s,t)
let Cases tl = withSort' <| Cases tl
let Application(t1,t2) = withSort' <| Application(t1,t2)
let Appl(f,s,tms) = withSort' <| App(f,s,Array.ofList tms)
let App(f,s,tms) = withSort' <| App(f,s,tms)
let Select(t1,t2) = withSort' <| Select(t1,t2)
#endif

type constructor = {cname:string;
                    tester:string;
                    projectors:list<string>;
                    sorts:list<Disj<sort, string>>;
                    recindexes:list<uint32>}
type op<'a> =
  | DefPrelude of string
  | DefSort  of sort * option<caption>
  | DefPred  of string * sort array * caption option
  | DeclFun  of string * sort array * sort * caption option
  | DefineFun of string * (string * sort) array * sort * term<'a> * caption option
  | DefData  of list<string * list<constructor>>
  | Assume   of term<'a> * caption option * assumptionId
  | Query    of term<'a>
  | Comment  of caption
  | Echo     of string
  | Mark     of Disj<lident, int>
with override x.ToString() = match x with 
  | DefPrelude s -> spr "(Prelude %s)" s
  | DefSort(s, _) -> spr "(DefSort %A)" s
  | DefPred(p, sorts, _) -> spr "(DefPred %s (%s))" p (String.concat " " (List.ofArray (Array.map (fun s -> spr "%A" s) sorts)))
  | DeclFun(s, sorts, sort, _) -> spr "(DeclFun %s (%s) %A)" s (String.concat " " (List.ofArray (Array.map (fun s -> spr "%A" s) sorts))) sort
  | DefineFun(s, sorts, sort, body, _) -> spr "(DefineFun %s (%s) %A\n %s)" s (String.concat " " (List.ofArray (Array.map (fun (nm,s) -> spr "(%s, %A)" nm s) sorts))) sort (body.ToString())
  | DefData dts -> spr "(declare-datatypes () (%s))"
      (String.concat "\n" <|
         (dts |> List.map (fun (d, constrs) -> 
                     let constrs = constrs |> List.map 
                         (fun c -> 
                           let cargs = List.map2 
                            (fun pname sort -> match sort with 
                               | Inl s -> spr "(%s %s)" pname (strSort s)
                               | Inr s -> spr "(%s %s)" pname s)
                            c.projectors c.sorts in 
                           let cargs = String.concat " " cargs in 
                             spr "(%s %s)" c.cname cargs) in
                       spr "(%s %s)" d (String.concat "\n" constrs))))
  | Assume(tm, _, aid) -> spr "(Assume[%s] %s)" (strOfAssumptionId aid) (tm.ToString())
  | Query tm -> spr "(Query %s)" (tm.ToString())
  | Comment c -> spr "(Comment %s)" c
  | Echo s -> spr "(Echo %s)" s
  | Mark (Inl lid) -> spr "(Mark %s)" (Pretty.sli lid)
  | Mark (Inr i) -> spr "(Mark %d)" i
end 
type ops<'a> = list<op<'a>>

let string_of_bvd_disj = function
    | Inl x -> string_of_bvd x
    | Inr y -> string_of_bvd y

type term'<'a> 
  with override x.ToString() = match comp' x with 
    | Hole(i) -> spr "[[%d]]" i 
    | Funsym s -> s
    | True -> "true"
    | False -> "false"
    | Integer i -> spr "(Int %d)" i
    | PP(p1,p2) -> spr "(PP %s %s)" (p1.ToString()) (p2.ToString())
    | BoundV(x, s, nm, _) ->  spr "(Bv %d :: %A (%s))" x s nm
    | FreeV(s, _) -> s
    | App(s, sort, tms) -> spr "(%s %s)" s (String.concat " " (List.map (fun x -> x.ToString()) (List.ofArray tms)))
    | Not t -> spr "(not %s)" (t.ToString())
    | And(t1,t2) -> spr "(and %s\n %s)" (t1.ToString()) (t2.ToString())
    | Or(t1,t2) ->  spr "(or %s\n %s)" (t1.ToString()) (t2.ToString())
    | Imp(t1,t2) -> spr "(imp %s\n %s)" (t1.ToString()) (t2.ToString())
    | Iff(t1,t2) -> spr "(iff %s\n %s)" (t1.ToString()) (t2.ToString())
    | Eq(t1,t2) ->  spr "(= %s\n %s)" (t1.ToString()) (t2.ToString())
    | LT(t1,t2) ->  spr "(< %s\n %s)" (t1.ToString()) (t2.ToString())
    | LTE(t1,t2) -> spr "(<= %s\n %s)" (t1.ToString()) (t2.ToString())
    | GT(t1,t2) ->  spr "(> %s\n %s)" (t1.ToString()) (t2.ToString())
    | GTE(t1,t2) -> spr "(>= %s\n %s)" (t1.ToString()) (t2.ToString())
    | Minus(t1) -> spr "(- %s)" (t1.ToString()) 
    | Add(t1,t2) -> spr "(+ %s\n %s)" (t1.ToString()) (t2.ToString())
    | Sub(t1,t2) -> spr "(- %s\n %s)" (t1.ToString()) (t2.ToString())
    | Mul(t1,t2) -> spr "(* %s\n %s)" (t1.ToString()) (t2.ToString())
    | Div(t1,t2) -> spr "(div %s\n %s)" (t1.ToString()) (t2.ToString())
    | Mod(t1,t2) -> spr "(mod %s\n %s)" (t1.ToString()) (t2.ToString())
    | Select(t1,t2) -> spr "(select %s\n %s)" (t1.ToString()) (t2.ToString())
    | Application(t1,t2) -> spr "(Appl %s %s)" (t1.ToString()) (t2.ToString())
    | IfThenElse(_,_,_, Some tm) -> tm.ToString()
    | IfThenElse(t1, t2, t3, None) -> spr "(ite %s\n %s\n %s)" (t1.ToString()) (t2.ToString()) (t3.ToString())
    | Forall(pats,_,xs,tm) -> spr "(Forall (%s) %s\n %s)" 
        (String.concat " " (List.map (fun (x, _) -> string_of_bvd_disj x) (List.ofArray xs)))
          (match pats with [] -> "" | _ -> spr "{:pattern %s}" (String.concat "; " (List.map (fun p -> p.ToString()) pats)))
          (tm.ToString())
    | Exists(pats,_,xs,tm) -> spr "(Exists (%s) %s\n %s)" 
        (String.concat " " (List.map (fun (x, _) -> string_of_bvd_disj x) (List.ofArray xs))) 
          (match pats with [] -> "" | _ -> spr "{:pattern %s}" (String.concat "; " (List.map (fun p -> p.ToString()) pats)))
          (tm.ToString())
    | Update(t1,t2,t3) -> spr "(update %s\n %s\n %s)" (t1.ToString()) (t2.ToString()) (t3.ToString())
    | ConstArray(s, _, tm) -> spr "(as const %s %s)" s (tm.ToString())
    | Z3Term tm -> "(Z3Term _)"
    | Cases tl -> spr "(Cases %s)" (String.concat "\n" (List.map (fun t -> t.ToString()) tl))
    | Residue(tm,_) -> spr "(Residue %s)" (tm.ToString())
    | ResFree tm -> spr "(ResFree %s)" (tm.ToString())
    | Function(x,s,tm) -> spr "(Fun %d %s)" x (tm.ToString())
 end

let rec termEq (x:term<'a>) (y:term<'a>) =
  match (comp x).tm, (comp y).tm with 
    | PP(a, _), _ -> termEq a y
    | _, PP(b, _) -> termEq x b
    | Funsym s, Funsym t -> s=t
    | True, True
    | False, False -> true
    | Integer i, Integer j -> i=j
    | BoundV(i, s, _, _), BoundV(j, t, _, _) -> i=j  && s=t
    | FreeV(x,s), FreeV(y,t) -> x=y && s=t
    | App(f,_,tl), App(g,_,sl) when tl.Length=sl.Length ->
        f=g && (Array.forall2 termEq tl sl)
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
    | Z3Term(t), Z3Term(s) -> t.Equals(s)
    | Cases(tl), Cases(sl) when tl.Length=sl.Length -> 
        List.forall2 termEq tl sl
    | Residue(t, x), Residue(s, y) -> termEq t s && x===y
    | ResFree t, ResFree s -> termEq t s
    | Hole x, Hole y -> x=y
    | Function(x, _, t1), Function(y,_,t2) -> termEq t1 t2 && x=y
    | Application(t1, t2), Application(s1,s2) -> termEq t1 s1 && termEq t2 s2
    | _ -> false


let incrBoundV increment tm = 
  let rec aux ix tm = match tm.tm with 
    | True
    | False
    | Integer _ 
    | FreeV _ -> tm
    | BoundV(i,s,xopt,r) -> 
        let _ = match !r with 
          | None -> ()
          | Some tm -> r := Some (aux ix tm) in
          if i >= ix then BoundV(i+increment, s, xopt, r) else tm
    | App(s,sort, tms) -> App(s, sort, Array.map (aux ix) tms)
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
    | IfThenElse(t1, t2, t3, None) ->  
        IfThenElse(aux ix t1, aux ix t2, aux ix t3, None)
    | IfThenElse(t1, t2, t3, Some t4) ->  
        IfThenElse(aux ix t1, aux ix t2, aux ix t3, Some (aux ix t4))
    | Forall(pats, sorts, names, tm) ->
        let ix = ix + Array.length sorts in 
          Forall(List.map (aux ix) pats, sorts, names, aux ix tm)
    | Exists(pats, sorts, names, tm) ->
        let ix = ix + Array.length sorts in 
          Exists(List.map (aux ix) pats, sorts, names, aux ix tm)
    | ConstArray(s, t, tm) -> ConstArray(s, t, aux ix tm)
    | Cases tl -> Cases (List.map (aux ix) tl)
    | Residue(tm, t) -> Residue(aux ix tm, t)
    | ResFree t -> ResFree(aux ix t)
    | Z3Term _ 
    | Hole _ -> tm
    | Function(x,s,tm) -> Function(x, s, aux ix tm)
    | Application(t1,t2) -> Application(aux ix t1, aux ix t2)
  in aux 0 tm

let flatten_forall fa =  
  let rec aux (binders, pats) = fun tm -> match tm.tm with 
    | Imp(guard, {tm=Forall(pats', sorts, names, body)}) -> 
        let guard = incrBoundV (sorts.Length) guard in 
          aux ((sorts, names)::binders, pats'@pats) (Imp(guard, body))
    | Forall (pats', sorts, names, body) -> 
        aux ((sorts, names)::binders, pats'@pats) body
    | _ -> 
        let sorts, names = List.unzip (List.rev binders) in
        let pats = List.rev pats in
          Forall(pats, Array.concat sorts, Array.concat names, tm) in
    aux ([],[]) fa

let flatten_exists ex = 
  let rec aux (binders, pats) = fun tm -> match tm.tm with
    | Exists (pats', sorts, names, body) -> 
        aux ((sorts, names)::binders, pats'@pats) body
    | _ -> 
        let sorts, names = List.unzip (List.rev binders) in
        let pats = List.rev pats in
          Exists(pats, Array.concat sorts, Array.concat names, tm) in
    aux ([],[]) ex  

let flatten_imp tm = 
  let mkAnd terms = match terms with 
    | [] -> raise Impos
    | hd::tl ->  List.fold_left (fun out term -> And(out, term)) hd tl in
  let rec aux out = fun tm -> match tm.tm with
    | Imp(x, y) -> aux (x::out) y
    | _ -> Imp(mkAnd (List.rev out), tm) in
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


(****************************************************************************)
(* Pretty printing Z3 terms and ops in SMT Lib format for debugging support *)
(****************************************************************************)
type TermLog() = class
  (*   [<Conditional("DEBUG")>] *)
  static member Log (oc,s) = (fpr oc "%s" s; oc.Flush())
end
let log oc s = TermLog.Log(oc,s)
let logopt oc s = match oc with None -> () | Some oc -> log oc s

type info      = { z3:Context; binders: Disj<btvdef,bvvdef> list; pp_name_map:HashMultiMap<string,string> }
let init_info z3 m = { z3=z3; binders = []; pp_name_map=m }

let map_pp info f = 
  if !Options.print_real_names 
  then f
  else
    match Hashtbl.tryfind info.pp_name_map f with 
      | Some g -> g
      | _ -> f 

let rec termToSmt (info:info) tm = 
  let tm = flatten_arrow tm in
  match (comp tm).tm with
  | True          -> "true"
  | False         -> "false"
  | Integer i     -> 
      if i < 0 then spr "(- %d)" (-i) 
      else spr "%d" i
  | PP(_,q) -> termToSmt info q
  | BoundV(i,_,_,_) as tm  -> 
      if (i < List.length info.binders) 
      then string_of_bvd_disj (List.nth info.binders i)
      else raise (Bad (spr "%A: Bad index for bound variable in formula" tm))
  | FreeV(x,_)    -> map_pp info x 
  | App(f,_,es) when es.Length=0 -> map_pp info f
  | App(f,_, es)     -> 
      (* let _ = if f="Select" then  *)
      (*   match es.(0) with  *)
      (*     | {tm=FreeV("x_0_2474", _);tmsort=tms} ->  *)
      (*         pr "Found offending term: %s\n Arg sort is %A\n" (tm.ToString()) tms *)
      (*     | _ -> ()  *)
      (* else () in  *)
      let f = map_pp info f in
      let a = Array.map (termToSmt info) es in
      let s = String.concat " " (Array.to_list a) in
        spr "(%s %s)" f s
  | Not(x)        -> spr "(not %s)" (termToSmt info x)
  | And(x,y)  -> 
      let conjuncts = flatten_and tm in 
        spr "(and %s)" (String.concat "\n" (List.map (termToSmt info) conjuncts))
  | Or(x,y) ->
      let disjuncts = flatten_or tm in 
        spr "(or %s)" (String.concat "\n" (List.map (termToSmt info) disjuncts))
  | Imp(x,y) -> spr "\n(implies %s\n %s)"(termToSmt info x)(termToSmt info y)
  | Iff(x,y) -> spr "(iff %s\n %s)" (termToSmt info x) (termToSmt info y)
  | Eq(x,y)  -> spr "(= %s\n %s)" (termToSmt info x) (termToSmt info y)
  | LT(x,y)  -> spr "(< %s %s)" (termToSmt info x) (termToSmt info y)
  | GT(x,y)  -> spr "(> %s %s)" (termToSmt info x) (termToSmt info y)
  | LTE(x,y) -> spr "(<= %s %s)" (termToSmt info x) (termToSmt info y)
  | GTE(x,y) -> spr "(>= %s %s)" (termToSmt info x) (termToSmt info y)
  | Minus(t1) -> spr "(- %s)" (termToSmt info t1)
  | Add(t1,t2) -> spr "(+ %s\n %s)" (termToSmt info t1) (termToSmt info t2)
  | Sub(t1,t2) -> spr "(- %s\n %s)" (termToSmt info t1) (termToSmt info t2)
  | Mul(t1,t2) -> spr "(* %s\n %s)" (termToSmt info t1) (termToSmt info t2)
  | Div(t1,t2) -> spr "(div %s\n %s)" (termToSmt info t1) (termToSmt info t2)
  | Mod(t1,t2) -> spr "(mod %s\n %s)" (termToSmt info t1) (termToSmt info t2)
  | Select(h,l)  -> spr "(select %s %s)" (termToSmt info h) (termToSmt info l)
  | Update(h,l,v) -> spr "(store %s %s %s)" (termToSmt info h) (termToSmt info l) (termToSmt info v)
  | IfThenElse(_, _, _, Some t4) -> termToSmt info t4
  | IfThenElse(t1, t2, t3, _) -> spr "(ite %s %s %s)" (termToSmt info t1) (termToSmt info t2) (termToSmt info t3)
  | Cases tms -> spr "(and %s)" (String.concat " " (List.map (termToSmt info) tms))
  | Forall(pats,x,y,z)
  | Exists(pats,x,y,z) as q -> 
      (* if pats.Length <> 0 then printfn "Patterned quantifier is %A\n" q; *)
      if Array.length x <> Array.length y 
      then raise (Bad "Unequal number of bound variables and their sorts")
      else
        let s = String.concat " "
          (Array.map (fun (a,b) -> spr "(%s %s)" (string_of_bvd_disj <| fst a) (strSort b))
             (Array.zip y x)) in
        let binders' = (List.rev (Array.to_list (Array.map fst y))) @ info.binders in
        let info' = { info with binders=binders' } in
          spr "\n\n(%s (%s)\n\n %s)" (strQuant q) s
            (if pats.Length <> 0 
             then spr "(! %s\n %s)" (termToSmt info' z) (patsToSmt info' pats)
             else termToSmt info' z)
  | Z3Term tm -> tm.ToString()
  | ConstArray(s, _, tm) -> spr "((as const %s) %s)" s (termToSmt info tm)
  | ResFree t -> termToSmt info t
  | x -> failwith (spr "Unexpected term form %A\n" x) 

and strQuant = function 
  | Forall _ -> "forall"
  | Exists _ -> "exists" 
  | _ -> raise Impos

and patsToSmt info  = function 
  | [] -> ""
  | pats -> spr "\n:pattern (%s)" (String.concat " " (List.map (fun p -> spr "%s" (termToSmt info p)) pats))
    
let strOfStrOpt = function Some x -> x | _ -> ""

let opToSmt info = function
  | DefPrelude p -> p
  | DefSort(tiio, msg_opt) -> 
      spr "\n(declare-sort %s) ; %s" (strSort tiio) (strOfStrOpt msg_opt)
  | Query(t)      -> spr "\n(assert (not %s)) \n (check-sat)" (termToSmt info t)
  | Comment(c)    -> spr "\n; %s" c
  | Mark (Inl l)        -> spr "\n; module %s" (Pretty.sli l)
  | Mark (Inr _) -> ""
  | DefPred(f,sorts,_) ->
      let f = map_pp info f in 
      let l = Array.to_list (Array.map strSort sorts) in
      spr "\n(declare-fun %s (%s) Bool)" f (String.concat " " l)
  | (DefData _) as dt -> dt.ToString()

  | DeclFun(f,argsorts,retsort,_) ->
      let f = map_pp info f in  
      let l = Array.to_list (Array.map strSort argsorts) in
        spr "\n(declare-fun %s (%s) %s)" f (String.concat " " l) (strSort retsort)

  | DefineFun(f,args,retsort,body,_) ->
      let f = map_pp info f in  
      let l = Array.to_list (Array.map (fun (nm,s) -> spr "(%s %s)" nm (strSort s)) args) in
      let info = args |> List.ofArray |> List.fold_left 
          (fun info (x,s) -> let x = ident(x,dummyRange) in {info with binders=(Inl (mkbvd (x,x)))::info.binders})
          info  in
        spr "\n(define-fun %s (%s) %s\n %s)" f (String.concat " " l) (strSort retsort) (termToSmt info body)
          
  | Assume(t,co,aid) ->
      let s = strOfAssumptionId aid in
      let c = match co with Some c -> spr ";;;;;;;;;;; %s (aid %s)\n" c s
                          | None -> spr   ";;;;;;;;;;; (aid %s)\n" s in
      spr "\n%s (assert %s)" c (termToSmt info t)
  | Echo s -> spr "(echo \"%s\")" s

let writeSmtFile info oc ops =
  if not !Options.logQueries then () 
  else
    begin
      log oc "\n;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n";
      log oc (spr "%s" (String.concat "\n" (List.map (opToSmt info) ops)));
      log oc "\n;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n";
      oc.Flush ()
    end

(****************************************************************************)
(* BUILDING Z3 Term from term                                               *)
(****************************************************************************)
type z3sort = Sort
type z3term = Expr

let seed = 
  let s = spr "%d" (System.DateTime.Now.Second) in
  (* let _ = pr "Seed is %s\n" s in *)
    s

let open_log =
  let f = ref false in
    (fun () -> 
       if not !f && !Options.z3log 
       then (ignore(Log.Open(Options.prependOutputDir "z3.log"));
             f:=true )
       else ())
      
let ini_params = 
  spr "%s \
       AUTO_CONFIG=false \
       MBQI=false \
       MODEL=true \
       MODEL_ON_TIMEOUT=true \
       RELEVANCY=2 \
       ARRAY_DELAY_EXP_AXIOM=false \
       ARRAY_EXTENSIONAL=false" (match !Options.z3timeout with None -> "" | Some s -> spr "/T:%d" ((int_of_string s) / 1000))

let mkZ3 () = 
  let _ = if !Options.z3log then open_log () else () in
  let options = [("SOFT_TIMEOUT", Options.getZ3Timeout());
                 ("AUTO_CONFIG", "false");
                 ("MBQI", "false");
                 ("MODEL", "true");
                 ("MODEL_ON_TIMEOUT", "true");
                 ("RELEVANCY", "2");
                 ("ARRAY_DELAY_EXP_AXIOM", "false");
                 ("ARRAY_EXTENSIONAL", "false");
                 ("RANDOM_SEED", seed)] in 
  let cfg = new System.Collections.Generic.Dictionary<string,string>() in 
  let _ = options |> List.iter (fun (k,v) -> cfg.Add(k,v)) in 
    new Context(cfg) 

type side = Both | Left | Right
let side_of_lid lid = 
  if Sugar.lid_equals lid Const.lproj_lid then Left 
  else if Sugar.lid_equals lid Const.rproj_lid then Right
  else raise Impos 

type array_sort<'a> = 
    {arr_sort:sort;
     arr_sel:(lident * (list<term<'a>> -> term<'a> -> term<'a> -> (term<'a> * term<'a>)));
     arr_upd:(lident * (list<term<'a>> -> term<'a> -> term<'a> -> term<'a> -> (term<'a> * term<'a>)));
     arr_emp:(lident * (term<'a> * term<'a>));
     arr_indom:(lident * (list<term<'a>> -> term<'a> -> term<'a> -> (term<'a> * term<'a>))); 
     arr_projector:side -> term<'a> -> term<'a>}

type sortMap<'a> = {
  arraySorts:list<lident * array_sort<'a>>;
  sortToZ3Sort: sort -> z3sort; 
  addSorts:list<sort*z3sort> -> unit;
  clearSorts:unit -> unit
}
    
type funSymMap = {
  addTfun : (lident * (string * sort * Sugar.logic_tag)) -> unit;
  isTfun : lident -> (string * sort * Sugar.logic_tag) option;
  defFunSym : string -> FuncDecl -> unit;
  addFunSyms : list<string * FuncDecl> -> unit;
  getFunSym : string -> FuncDecl;
  getFunSyms : unit -> list<string * FuncDecl>;
  clearFunSyms : unit -> unit
}
    
type ptermctx<'a> = {
  id:string option;
  z3ctx:Context;
  z3solver:Solver;
  sortMap:sortMap<'a>;
  funSymMap:funSymMap;
  stream:System.IO.StreamWriter option
}

let lookup_array_function termctx lid = 
  match termctx.sortMap.arraySorts |> Util.findOpt
      (fun (_, a) -> (Sugar.lid_equals lid (fst a.arr_sel) ||
                        Sugar.lid_equals lid (fst a.arr_upd) ||
                        Sugar.lid_equals lid (fst a.arr_emp) ||
                        Sugar.lid_equals lid (fst a.arr_indom))) with 
        | None -> None
        | Some (_, a) -> Some a

let is_array_select termctx lid = 
  match lookup_array_function termctx lid with 
    | Some a -> Sugar.lid_equals lid (fst a.arr_sel)
    | None -> false
        
let is_array_function termctx lid = 
  match lookup_array_function termctx lid with 
    | Some _ -> true
    | None -> false
      
let lookupArraySort termctx t = 
  match (AbsynUtils.unrefine (unascribe_typ t)).v with 
    | Typ_const(tc, _) -> 
        (match termctx.sortMap.arraySorts |> Util.findOpt (fun (lid, _) -> Sugar.lid_equals tc.v lid) with 
           | Some (_, r) -> Some r
           | _ -> None)
    | _ -> None

let mkSortMap (z3:Context) : sortMap<'a> = 
  let sorts = ref [] in 
  let rec sortToZ3 s = match Util.findOpt (fun (s', _) -> s=s') !sorts with
    | Some (_, z3sort) -> z3sort
    | None -> 
        let z3sort = match s with
          | Int_sort -> z3.MkIntSort() :> Sort
          | Array(s1, s2) -> z3.MkArraySort(sortToZ3 s1, sortToZ3 s2) :> Sort
          | s -> z3.MkUninterpretedSort (strSort s) :> Sort in
          sorts := (s,z3sort)::!sorts;
          z3sort in 
    {sortToZ3Sort=sortToZ3;
     arraySorts=[];
     addSorts=(fun smap -> sorts := smap@(!sorts)); 
     clearSorts=(fun () -> sorts := [])}

let mkFunSymMap () : funSymMap =       
  let x = Hashtbl.create 1000 in
  let tfuns = ref [] in
    {addTfun = (fun lid -> tfuns := lid::!tfuns);
     isTfun = (fun lid -> match Util.findOpt (fun (lid',_) -> Sugar.lid_equals lid' lid) !tfuns with
                 | None -> None 
                 | Some (_, v) -> Some v);
     defFunSym=(fun s fd -> Hashtbl.add x s fd);
     addFunSyms=(fun sfds -> List.iter (fun (s,fd) -> Hashtbl.add x s fd) sfds);
     getFunSym=(fun s ->
                  match Hashtbl.tryfind x s with
                    | None ->
                        let msg = spr "GetFunSym failed on symbol: %s" s in
                          pr "%s\n" msg;
                          raise (Bad msg)
                    | Some x -> x);
     getFunSyms=(fun () -> Hashtbl.fold (fun s fd out -> (s,fd)::out) x []);
     clearFunSyms=(fun () -> Hashtbl.clear x)}

let tctxConst : ptermctx<unit> = 
  let z3 : Context =  mkZ3() in 
    {id=None;
     z3ctx=z3;
     z3solver=z3.MkSolver();
     sortMap=mkSortMap z3;
     funSymMap=mkFunSymMap();
     stream=None}

let cleanup () = if tctxConst.z3ctx <> null then tctxConst.z3ctx.Dispose()

let rec termToZ3Term tctx tm = 
  let z3ctx = tctx.z3ctx in 
  let sortToZ3Sort = tctx.sortMap.sortToZ3Sort in 
  let getFunSym = tctx.funSymMap.getFunSym in 
  let rec termToBoolExpr tm = termToZ3Term tm :?> BoolExpr
  and termToArithExpr tm = termToZ3Term tm :?> ArithExpr
  and termToIntExpr tm = termToZ3Term tm :?> IntExpr
  and termToZ3Term tm : Expr = match (comp (flatten_arrow tm)).tm with 
    | ResFree t      -> termToZ3Term t
    | True           -> z3ctx.MkTrue () :> Expr
    | False          -> z3ctx.MkFalse () :> Expr
    | Integer i      -> z3ctx.MkInt i :> Expr
    | PP(a,_)        -> termToZ3Term a
    | BoundV(i,s,_,_)   -> z3ctx.MkBound (uint32 i, sortToZ3Sort s) :> Expr
    | FreeV(x,s)    -> z3ctx.MkConst (x, sortToZ3Sort s) :> Expr
    | App(f,_,es) when es.Length = 0 -> z3ctx.MkConst(getFunSym f) :> Expr
    | App(f,_,es)   -> 
        let z3f = getFunSym f in 
        let args = Array.map termToZ3Term es in 
        let result = z3ctx.MkApp (z3f, args) in 
          result :> Expr
    | Not(x)        -> z3ctx.MkNot (termToBoolExpr x) :> Expr
    | And(x,y)      -> z3ctx.MkAnd [|termToBoolExpr x;
                                  termToBoolExpr y|] :> Expr
    | Or(x,y)       -> z3ctx.MkOr [|termToBoolExpr x; termToBoolExpr y|] :> Expr
    | Imp(x,y)      -> z3ctx.MkImplies (termToBoolExpr x, termToBoolExpr y) :> Expr
    | Iff(x,y)      -> z3ctx.MkIff (termToBoolExpr x, termToBoolExpr y) :> Expr
    | Eq(x,y)       -> z3ctx.MkEq (termToZ3Term x, termToZ3Term y) :> Expr
    | LT(x,y)       -> z3ctx.MkLt (termToArithExpr x, termToArithExpr y) :> Expr
    | GT(x,y)       -> z3ctx.MkGt (termToArithExpr x, termToArithExpr y) :> Expr
    | LTE(x,y)      -> z3ctx.MkLe (termToArithExpr x, termToArithExpr y) :> Expr
    | GTE(x,y)      -> z3ctx.MkGe (termToArithExpr x, termToArithExpr y) :> Expr 
    | Minus(x)      -> z3ctx.MkUnaryMinus (termToArithExpr x) :> Expr
    | Add(x,y)      -> z3ctx.MkAdd (termToArithExpr x, termToArithExpr y) :> Expr
    | Sub(x,y)      -> z3ctx.MkSub (termToArithExpr x, termToArithExpr y) :> Expr
    | Mul(x,y)      -> z3ctx.MkMul (termToArithExpr x, termToArithExpr y) :> Expr
    | Div(x,y)      -> z3ctx.MkDiv (termToArithExpr x, termToArithExpr y) :> Expr
    | Mod(x,y)      -> z3ctx.MkMod (termToIntExpr x, termToIntExpr y) :> Expr
    | Cases tms     -> z3ctx.MkAnd (Array.ofList (List.map termToBoolExpr tms)) :> Expr
    | Select(h,l)   -> 
        let z3h = termToZ3Term h in 
        let z3l = termToZ3Term l in 
        let result =  z3ctx.MkSelect(z3h :?> ArrayExpr, z3l) in 
          result :> Expr
    | Update(h,l,v) -> z3ctx.MkStore(termToZ3Term h :?> ArrayExpr, 
                                  termToZ3Term l, 
                                  termToZ3Term v) :> Expr
    | IfThenElse(t1, t2, t3, _) -> z3ctx.MkITE(termToBoolExpr t1, termToZ3Term t2, termToZ3Term t3)  :> Expr
    | Forall(pats, sorts, names, body) ->  
        let body = termToZ3Term body in 
        let patterns = patsToPattern tctx pats in
          z3ctx.MkForall (Array.map sortToZ3Sort sorts, 
                       Array.map (fun (x,_) -> z3ctx.MkSymbol(string_of_bvd_disj x) :> Symbol) names, 
                       body,
                       1u, 
                       patterns, 
                       null, 
                       null,
                       null) :> Expr

    | Exists(pats, sorts, names, body) -> 
        let body = termToZ3Term body in 
        let patterns = patsToPattern tctx pats in
          z3ctx.MkExists(Array.map sortToZ3Sort sorts, 
                      Array.map (fun (x,_) -> z3ctx.MkSymbol(string_of_bvd_disj x) :> Symbol) names, 
                      body,
                      1u, 
                      patterns, 
                      null, 
                      null, 
                      null)  :> Expr
    | ConstArray(_, Array(domain, _), tm) as tm' -> 
        let result = z3ctx.MkConstArray(sortToZ3Sort domain, termToZ3Term tm)  in
          result :> Expr
    | Z3Term tm -> tm 
    | x -> failwith (spr "Unexpected term form %A\n" x) 

  in 
    termToZ3Term tm

and patsToPattern tctx : list<pat<'a>> -> array<Pattern> = function
  | [] -> [||]
  | pats ->
      let exprs = pats |> List.map (fun p -> (termToZ3Term tctx p)) |> Array.ofList in 
      let pat = tctx.z3ctx.MkPattern(exprs) in 
        [| pat |]

let mkProj n i = 
  if !Options.encodingdt 
  then spr "Primitive_%s_proj_%d" n i   
  else spr "%s_proj_%d" n i   

let mkTester n = spr "is-%s" n 

let mkFuncdecls (z3:Context) (l:list<Constructor>) = l |> List.collect 
    (fun c -> 
       let fd = c.ConstructorDecl in 
       let nm = fd.Name.ToString() in
       let accessors = c.AccessorDecls in
       let tester = c.TesterDecl in 
       let _, fds = (List.ofArray accessors) |> List.fold_left (fun (i, out) a -> (i+1, (a.Name.ToString()(* mkProj nm i *), a)::out)) (0, [])  in
         (nm, fd)::(tester.Name.ToString()(* mkTester nm *), tester)::fds)
      
let opToZ3 tctx = 
  let z3ctx = tctx.z3ctx in 
  let z3solver = tctx.z3solver in 
  let sortToZ3Sort = tctx.sortMap.sortToZ3Sort in 
  let defFunSym = tctx.funSymMap.defFunSym in
    function 
      | DefSort(s, _)    -> ignore (sortToZ3Sort s)
      | DefPred(f,ts,_)  -> defFunSym f (z3ctx.MkFuncDecl (f, Array.map sortToZ3Sort ts, z3ctx.MkBoolSort()))
      | DeclFun(f,ts,t,_) -> defFunSym f (z3ctx.MkFuncDecl (f, Array.map sortToZ3Sort ts, sortToZ3Sort t))
      | DefineFun(f,args,ret,body,_) -> defFunSym f (z3ctx.MkFuncDecl(f, Array.map (fun (_, s) -> sortToZ3Sort s) args, sortToZ3Sort ret))
      | DefData(dts) -> 
          let cases = dts |> List.map 
              (fun (dname, constrs) -> 
                 let constrs = constrs |> List.map 
                     (fun c -> z3ctx.MkConstructor(c.cname, spr "is-%s" (c.cname), 
                                                Array.ofList (c.projectors), 
                                                Array.ofList <| (c.sorts |> List.map (function 
                                                                                        | Inl s -> sortToZ3Sort s
                                                                                        | Inr _ -> null)), 
                                                Array.ofList c.recindexes)) in 
                   dname, Array.ofList constrs) in 
          let cnames, constrs = List.unzip cases in 
          let dts = z3ctx.MkDatatypeSorts(Array.ofList (List.map (fun (c:string) -> z3ctx.MkSymbol(c) :> Symbol) cnames), 
                                       Array.ofList constrs) in
          let _ = cnames |> List.mapi (fun i c -> tctx.sortMap.addSorts ([Ext c, dts.(i) :> z3sort])) in 
          let fds = mkFuncdecls z3ctx (List.collect (fun c -> List.ofArray c) constrs) in 
            tctx.funSymMap.addFunSyms fds
      | Assume(t,_,aid)  -> z3solver.Assert (termToZ3Term tctx t :?> BoolExpr)
      | Echo _
      | DefPrelude _
      | Comment _ 
      | Mark _     -> ()

let handleZ3Error msg =  
  stdout.Flush ();
  stream_query (fun s -> s.Flush());
  failwith (spr "\n\n  Z3 rejected operation on operation %s\n\n" (msg.ToString()))
    (* when this error gets thrown, it's useful to run make smt *)
    
let opsToZ3 tctx ops : unit =
  let curOp = ref None in
    try 
      List.iter (fun op -> curOp := Some op; opToZ3 tctx op) ops
    with 
        :? ZZZError as e  -> 
      (pr "%s" (e.ToString());handleZ3Error !curOp)
      
(****************************************************************************)
(* CHECKING Z3 ANSWER TO QUERY                                              *)
(****************************************************************************)
type z3status = SAT | UNSAT | UNKNOWN | TIMEOUT

let doZ3Exe ini_params = 
  let parse (z3out:string) = 
    let lines = List.ofArray (z3out.Split([|'\n'|])) |> List.map (fun l -> l.Trim()) in 
    let rec lblnegs lines = match lines with 
      | lname::"false"::rest -> lname::lblnegs rest
      | lname::_::rest -> lblnegs rest
      | _ -> [] in
    let rec result = function
      | "timeout"::tl -> TIMEOUT, []
      | "unknown"::tl -> UNKNOWN, lblnegs tl
      | "sat"::tl -> SAT, lblnegs tl
      | "unsat"::tl -> UNSAT, []
      | _::tl -> result tl 
      | _ -> pr "Got output lines: %s\n" (String.concat "\n" (List.map (fun (l:string) -> spr "<%s>" (l.Trim())) lines)); raise Impos in
      result lines in
  let file = queryFile () in 
  let cmdargs = spr "%s %s" ini_params file in 
  let pinfo = new ProcessStartInfo("z3.exe", cmdargs) in 
  pinfo.RedirectStandardOutput <- true;
  pinfo.RedirectStandardError <- true;
  pinfo.UseShellExecute <- false;
  let proc = new Process() in
  proc.StartInfo <- pinfo;
  let result = proc.Start() in 
  let stdout = proc.StandardOutput.ReadToEnd() in
  let stderr = proc.StandardError.ReadToEnd() in 
    if result 
    then 
      let status, lblnegs = parse (stdout.Trim()) in
        status, lblnegs, cmdargs
    else raise (Bad "Z3 returned an error")
    result
      
let callZ3Exe stream labels = 
  labels |> List.iter (fun (lname, {tm=FreeV(x,_)}) -> logopt stream (spr "(echo \"%s\")\n(eval %s)\n" lname x));
  let rec proc_result again (status, lblnegs, cmdargs) = 
    match status with 
      | UNSAT -> true
      | _ -> 
          pr "Called z3.exe %s\nZ3 says: %A\n" cmdargs status;
          match status with 
            | UNKNOWN when !Options.mbqi && again -> 
                pr "Trying again with MBQI ... \n";
                proc_result false (doZ3Exe (ini_params ^ " MBQI=true"))
            | _ -> 
                pr "Failing assertions: %s\n" (String.concat "\n\t" lblnegs);
                false in 
    proc_result true (doZ3Exe ini_params)

let processZ3Answer stream labels (z3ctx:Context, z3solver:Solver) (x:Expr) : bool =
  let report_failing_assertions (model:Model) = 
    let is_label_neg (lname, {tm=(FreeV(x,s))}) =
      let tm = z3ctx.MkConst(x, z3ctx.MkBoolSort()) in 
        model.Eval(tm).IsFalse in 
    let _ = match labels |> Util.findOpt is_label_neg with 
      | Some (lname, _) -> pr "Assertion %s failed\n" lname
      | None -> pr "Unable to detect failing assertion\n" in
      ()
      (* (!model).Dispose() *)
  in
  if !Options.z3exe 
  then callZ3Exe stream labels
  else
    let status =
      Profiling.profile
        (fun () -> 
           z3solver.Assert(x :?> BoolExpr);
           z3solver.Check())
        "Z3 query" in
      if status = Status.UNSATISFIABLE  then true
      else 
        let _ = report_failing_assertions z3solver.Model in 
        let msg = if status=Status.SATISFIABLE then "satisfiable" else "unknown result" in
          pr "\nZ3 : %s\n" msg;
          stream_query (fun s -> log s (spr "; unsat? %s\n" msg)); 
          stream_query (fun s -> s.Flush());
          false
            
let logQueryToZ3 info stream tctx = function 
  | Query(t) -> 
      (try 
         if !Options.logQueries then 
           (log stream (opToSmt info (Query t)));
         processZ3Answer (Some stream) [] (tctx.z3ctx, tctx.z3solver) (termToZ3Term tctx (Not t))
       with 
           :? ZZZError -> handleZ3Error (Not t))
  | _ -> raise (Bad "queryToZ3 called with non-query")

let queryToZ3 tctx = function 
  | Query(t) -> 
      (try 
         tctx.z3solver.Push();
         let res = processZ3Answer tctx.stream [] (tctx.z3ctx,tctx.z3solver) (termToZ3Term tctx (Not t)) in
         let _ = tctx.z3solver.Pop() in 
           res
       with 
           :? ZZZError -> handleZ3Error (Not t))
  | _ -> raise (Bad "queryToZ3 called with non-query")
      
let queriesToZ3 info stream tctx qs = 
  List.forall (fun q -> logQueryToZ3 info stream tctx (Query q)) qs
      
let logQuery z3 pp_name_map allOps = 
  let allOps = List.rev allOps in 
  let info = init_info z3 pp_name_map in
  let stream = new System.IO.StreamWriter (queryFile ()) in
  let _ = pr "Writing to query file %s\n" (queryFile ()) in
  let _ = writeSmtFile info stream allOps in 
    stream.Flush (); 
    stream.Close ()
      
let logOps z3 stream pp_name_map allOps = 
  if !Options.logQueries 
  then 
    let info = init_info z3 pp_name_map in
    let _ = writeSmtFile info stream allOps in 
      stream.Flush ()
  else ()
    
let openStream ix = 
  let nm = spr "%s%s" (queryFile ()) ix in
  let stream = new System.IO.StreamWriter(nm) in 
  let _ = pr "Writing to query file %s\n" nm in
    stream

let assertOps z3 ops qopt : bool =
  let _ = opsToZ3 z3 ops in 
    match qopt with 
      | None -> false
      | Some q -> queryToZ3 z3 q

let pushOps tctx ops = 
  match ops with 
    | [] -> ()
    | _ -> 
        let query,  ops = List.partition (function Query _ -> true | _ -> false) ops in
        let _ = match query with 
          | [] -> assertOps tctx ops None
          | _ -> raise Impos (* should never push a query *) in
          tctx.z3solver.Push()
      
let queryZ3 tctx ops : bool = 
  let query,  ops = List.partition (function Query _ -> true | _ -> false) ops in
  let query = match query with 
    | [] -> raise Impos
    | [q] -> q in
  let _ = tctx.z3solver.Push() in
  let result = assertOps tctx ops (Some query) in
  let _ = tctx.z3solver.Pop() in
    result


(* Builders ... lifted from basic.fs *)
let btvName =  "Typ_btvar"
let btvInv =  "Typ_btvar_inv"
let mk_Typ_btvar i = App(btvName, Arrow(Int_sort, Type_sort), [| Integer i |])
let mk_Typ_btvar_term t = App(btvName, Arrow(Int_sort, Type_sort), [| t |])
let mkBtvInv t = App(btvInv, Arrow(Type_sort, Int_sort), [| t |])

let bvName =  "Exp_bvar"
let bvInv =  "Exp_bvar_proj_0"
let mk_Exp_bvar i = App(bvName, Arrow(Int_sort, Term_sort), [| Integer i |])
let mk_Exp_bvar_term t = App(bvName, Arrow(Int_sort, Term_sort), [| t |])
let mkBvInv t = App(bvInv, Arrow(Term_sort, Int_sort), [| t|])

let mkTerm name = FreeV(name, Term_sort)
let mkType name = FreeV(name, Type_sort)
//let mkApp term terms = App(term, Array.ofList terms)
let mkAnd (terms:list<term<'a>>) : term<'a> = match terms with 
  | [] -> raise Impos
  | hd::tl ->  List.fold_left (fun out term -> And(out, term)) hd tl
let mkOr terms = match terms with 
  | [] -> raise Impos
  | hd::tl ->  List.fold_left (fun out term -> Or(out, term)) hd tl
let check_pat_vars r pats sorts = 
  if List.length pats = 0 
  then ()
  else 
    let bvars = List.collect free_bvars pats in 
    sorts |> List.iteri (fun i sort -> 
      if not (List.exists (fun (i',_) -> i=i') bvars)
      then raise (Error(spr "Pattern does not include bound variable %d of sort %A\n%s" i sort 
                          (String.concat "; " (List.map (fun t -> t.ToString()) pats)), r)))
let mkPatsForall r pats sorts names guard_opt body = 
  check_pat_vars r pats sorts;
  let body = match guard_opt with 
    | Some tm -> Imp(tm,body)
    | _ -> body in 
   Forall(pats, Array.ofList sorts, Array.ofList names, body)
let mkForall sorts names guard_opt body : term<'a> = 
  mkPatsForall dummyRange [] sorts names guard_opt body
let mkPatsExists r pats sorts names guard_opt body = 
  check_pat_vars r pats sorts;
  let body = match guard_opt with 
    | Some tm -> And(tm,body)
    | _ -> body in 
    Exists(pats, Array.ofList sorts, Array.ofList names, body)
let mkExists sorts names guard_opt body = 
  mkPatsExists dummyRange [] sorts names guard_opt body 
let mkFunSym name argSorts sort = DeclFun(name, Array.ofList argSorts, sort, None)
let mkConstant name sort = DeclFun(name, [| |], sort, None)
let mkPred name argSorts = DefPred(name, Array.ofList argSorts, None)
let mkAssumption name phi = 
  let n = spr "assumption::%s" name in 
    Assume(phi, None, AName n)
let funPPNameOfBvar bv = spr "Term_%s" ((bvar_ppname bv).idText)

(* let funNameOfBvar bv = spr "Term_fvarold_%s" ((bvar_real_name bv).idText) *)
(* let funNameOfBvdef bvd sfx = spr "Term_fvarold_%s__%d" (string_of_bvd bvd) sfx *)
(* let funNameOfLid lid =  *)
(*   spr "Term_fvarold_%s"  *)
(*     (if Const.is_tuple_data_lid lid *)
(*      then Pretty.str_of_lident Const.tuple_UU_lid *)
(*      else Sugar.text_of_lid lid) *)

let cleanString b = 
  let chars = Util.unicodeEncoding.GetChars(b) in
  if chars |> Array.forall (fun c -> System.Char.IsDigit(c) || System.Char.IsLetter(c) || c='_')
  then new System.String(chars)
  else System.Convert.ToBase64String(b)
    
let clean_id (str:string) = str.Replace("'", "/") (* / is a valid identifier char in smt2 but not '; vice versa for F* *)
let invName str ix = spr "%s_proj_%d" str ix
let predNameOfLid lid = spr "Pred_%s" (clean_id (Sugar.text_of_lid lid))
let typePPNameOfBvar bv = spr "Type_%s" (clean_id ((bvar_ppname bv).idText))
let typeNameOfUvar uv = spr "Type_uv_%d" (Unionfind.uvar_id uv)
let typeNameOfBtvar btv = spr "Type_%s" (clean_id ((bvar_real_name btv).idText))
let typeNameOfBvdef bvd sfx = spr "Type_%s__%d" (clean_id (string_of_bvd bvd)) sfx
let typeNameOfLid lid = spr "Type_name_%s" (clean_id (Sugar.text_of_lid lid))
let recordConstrName lid = spr "Term_constr_make_%s" (clean_id (Sugar.text_of_lid lid))
let recordConstrLid lid = asLid [ident(spr "make_%s" (Sugar.text_of_lid lid), 0L)]
let arrConstrName lid = spr "Term_arr_%s" (clean_id (Sugar.text_of_lid lid))

let funNameOfBvar bv = spr "Term_bvar_%s" (clean_id ((bvar_real_name bv).idText))
let funNameOfBvdef bvd  = spr "Term_bvar_%s" (clean_id (string_of_bvd bvd) )
let funNameOfBvdef_sfx bvd sfx  = spr "Term_bvar_%s_%d" (clean_id (string_of_bvd bvd)) sfx
let funNameOfFvar lid = 
  spr "Term_fvar_%s" 
    (if Const.is_tuple_data_lid lid
     then Pretty.str_of_lident Const.tuple_UU_lid
     else clean_id (Sugar.text_of_lid lid))
let funNameOfConstr lid = 
  spr "Term_constr_%s" 
    (if Const.is_tuple_data_lid lid
     then Pretty.str_of_lident Const.tuple_UU_lid
     else clean_id (Sugar.text_of_lid lid))
    
let tfunNameOfLid lid = 
  spr "Type_fun_%s" (clean_id (Sugar.text_of_lid lid))

open KindAbbrevs
let mkEq env e1 e2 = 
  let eqK = Tcenv.lookup_typ_lid env Const.eq_lid in 
  let eqT = twithsort (Typ_const(twithsort Const.eq_lid eqK, None)) eqK in 
    setsort (AbsynUtils.mkTypApp eqT [AbsynUtils.unrefine e1.sort] [e1;e2]) Kind_erasable 


let destruct tenv typ lid = 
  match AbsynUtils.flattenTypAppsAndDeps (AbsynUtils.strip_pf_typ typ) with 
    | {v=Typ_const(tc,_)}, args when Sugar.lid_equals tc.v lid -> Some args
    | _ -> None

let rec norm tcenv t = 
  let t = 
    if AbsynUtils.is_pf_typ t 
    then norm tcenv (AbsynUtils.strip_pf_typ t)
    else t in
    alpha_convert <| Tcutil.reduce_typ_delta_beta tcenv t

exception Single_sided of (string * Range.range)

let rec project_vars_or_duplicate env t = 
  let reduce_kte env rk rt re t = 
    AbsynUtils.reduce_typ 
      rk rt re 
      AbsynUtils.combine_kind
      AbsynUtils.combine_typ 
      AbsynUtils.combine_exp 
      env [] t in
  let reduce env rt re t = reduce_kte env (fun v _ _ -> v) rt re t in
  let mk_exists =
    let ek = Tcenv.lookup_typ_lid env Const.exists_lid in 
    let exists_typ = twithsort (Typ_const(fvwithsort Const.exists_lid ek, None)) ek in
    fun x t ->
      let inst_kind = open_kind ek x.sort in 
        twithsort 
          (Typ_app (twithsort (Typ_app(exists_typ, x.sort)) inst_kind,
                    twithsort (Typ_lam(x.v, x.sort, t)) (Kind_dcon(None, x.sort, Kind_erasable))))
          Kind_erasable in
  let proj_t = Tcenv.lookup_lid env Const.lproj_lid in 
  let mkproj lid e =
    let t = project_vars_or_duplicate env e.sort in 
      ewithsort (Exp_constr_app(ewithsort lid proj_t, [t], [], [e])) t in 
  let bound binders x = match findOpt (function Inl _ -> false | Inr y -> bvd_eq x.v y) binders with 
    | None -> false
    | Some _ -> true in 

  let rec project_to_leaves t = 
    let rec re rk rt ve inside binders top_exp : (exp * side) =
      let reduce_exp move_inside exp = re rk rt ve move_inside binders exp in 
      let proj_if msgexp side exp = 
        if inside <> Both 
        then raise (Single_sided(spr "(%A) Relational formula has a nested projection: %s\n" inside (Pretty.strExp top_exp), top_exp.p))
        else reduce_exp side exp in

      let exp = unascribe top_exp in 
        match exp.v with 
          | Exp_bvar x -> 
              (match inside with 
                 | Both -> 
                     if bound binders x then exp, inside
                     else raise (Single_sided(spr "Double-sided variables in relational formulas must be bound; found a free variable %s\n" (Pretty.strBvar x), x.p))
                 | Left -> mkproj Const.lproj_lid exp, inside
                 | Right -> mkproj Const.rproj_lid exp, inside)
          | Exp_fvar _ -> 
              (match inside with 
                 | Both -> 
                     raise (Single_sided(spr "Double-sided variables in relational formulas must be bound; found a free variable %s\n" (Pretty.strExp exp), exp.p))
                 | Left -> mkproj Const.lproj_lid exp, inside
                 | Right -> mkproj Const.rproj_lid exp, inside)
          | Exp_constr_app(lproj, [t], _, [v]) when Sugar.lid_equals lproj.v Const.lproj_lid -> 
              let (e, _) = proj_if exp Left v in e, inside
          | Exp_constr_app(rproj, [t], _, [v]) when Sugar.lid_equals rproj.v Const.rproj_lid -> 
              let (e, _) = proj_if exp Right v in e, inside
          | _ -> let (e, _) = ve inside binders exp in (e, inside) in
      
    let rec rt rk vt ve side binders t : (typ * side) =
      try 
        let t' = norm env (unascribe_typ t) in 
          match destruct env t' Const.doublesided_lid  with
            | Some [Inl arg] -> duplicate arg, side
            | _ -> 
                let tt = t' in
                match t'.v with 
                  | Typ_refine(x,t,phi,g) -> 
                      let phi = project_vars_or_duplicate env phi in 
                      let t,_ = rt rk vt ve side binders t in 
                        twithinfo (Typ_refine(x,t,phi,g)) t'.sort t'.p, side

                  | Typ_app({v=Typ_app(t,_); sort=s1}, t2)
                      when (let t = unascribe_typ t in
                              AbsynUtils.is_constructor t Const.forall_lid ||
                              AbsynUtils.is_constructor t Const.forallP_lid ||
                                AbsynUtils.is_constructor t Const.forallA_lid ||
                                AbsynUtils.is_constructor t Const.exists_lid ||
                                AbsynUtils.is_constructor t Const.existsP_lid ||
                                AbsynUtils.is_constructor t Const.existsA_lid) ->
                      (match unascribe_typ t2 with
                         | {v=Typ_lam(x, t1, t2); sort=s2} ->
                             let binders = AbsynUtils.push_vbinder binders (Some x) in
                             let t1, _ = vt side binders t1 in
                             let t2, _ = vt side binders t2 in
                               (* let _ = pr "Reached case for %s\n" (Pretty.strTyp t1) in *)
                               twithsort  (Typ_app(twithsort (Typ_app(t, t1)) s1,
                                                   twithsort (Typ_lam(x, t1, t2)) s2)) tt.sort, side
                         | _ -> raise Impos)


                  | _ -> let (t, _) = vt side binders t' in (t, side)
      with Single_sided(msg, p) as e -> (pr "Failed to project type %s\n" (Pretty.strTyp t); raise e)
    in 
      reduce Both rt re t 

  and shift sidelid t = 
    let rt rk vt re sidelid binders top_t = 
      let t = norm env (unascribe_typ top_t) in 
      let tt = t in
        match t.v with 
          | Typ_app({v=Typ_const(r,_)}, arg) when Sugar.lid_equals r.v Const.reln_lid -> 
              (* let _ = pr "Found relational formula within double-sided type: %s\n" (Pretty.strTyp t) in *)
              let t, _ = project_to_leaves arg in 
              (* let t = List.fold_right mk_exists exs t in  *)
              (* let _ = pr "Found relational formula within double-sided type\n Projected to: %s\n" (Pretty.strTyp t) in *)
                t, sidelid

          (* | Typ_app({v=Typ_app(t,_); sort=s1}, t2) *)
          (*     when (let t = unascribe_typ t in *)
          (*             AbsynUtils.is_constructor t Const.forall_lid || *)
          (*               AbsynUtils.is_constructor t Const.forallA_lid ||  *)
          (*               AbsynUtils.is_constructor t Const.exists_lid ||  *)
          (*               AbsynUtils.is_constructor t Const.existsA_lid) ->  *)
          (*     (match unascribe_typ t2 with  *)
          (*        | {v=Typ_lam(x, t1, t2); sort=s2} ->  *)
          (*            let binders = AbsynUtils.push_vbinder binders (Some x) in  *)
          (*            let t2, _ = vt sidelid binders t2 in  *)
          (*            let _ = pr "Reached case for %s\n" (Pretty.strTyp t1) in  *)
          (*              twithsort  (Typ_app(twithsort (Typ_app(t, t1)) s1,  *)
          (*                                  twithsort (Typ_lam(x, t1, t2)) s2)) tt.sort, sidelid *)
          (*        | _ -> raise Impos) *)

          | _ -> 
              match destruct env tt Const.doublesided_lid with
                | Some [Inl arg] -> vt sidelid binders arg
                | _ -> vt sidelid binders t in
      
    let re rk rt ve sidelid binders top_exp =
      let exp = unascribe top_exp in 
        match exp.v with 
          | Exp_constr_app(l, [t], _, [v]) 
              when (Sugar.lid_equals l.v Const.lproj_lid ||
                    Sugar.lid_equals l.v Const.rproj_lid) -> 
              raise (Single_sided(spr "Shifting to the %s\nSingle-sided variable in double-sided formula: %s" (Pretty.sli sidelid) (Pretty.strExp top_exp), top_exp.p))
          | Exp_bvar x -> 
              if bound binders x then exp, sidelid
              else mkproj sidelid exp, sidelid
          | _ -> ve sidelid binders exp in 
      fst <| reduce sidelid rt re t 
          
  and duplicate t = 
    let dup_formula t = setsort (AbsynUtils.mkAnd (shift Const.lproj_lid t) (shift Const.rproj_lid t)) Kind_erasable  in
    let rk vk _ _ _ binders k = vk () binders k in
    let rec rt rk vt re () binders top_t = 
      let t = norm env (unascribe_typ top_t) in 
      let tt = t in 
        match destruct env tt Const.doublesided_lid with
          | Some [Inl arg] -> vt () binders arg
          | _ -> 
              match tt.v with  
                | Typ_refine(x, t, phi, ghost) -> 
                    let t, _ = rt rk vt re () binders t in 
                    let phi = dup_formula phi in 
                      twithinfo (Typ_refine(x, t, phi, ghost)) t.sort t.p, ()
                        
                (* | Typ_app({v=Typ_app(t,_); sort=s1}, t2) *)
                (*     when (let t = unascribe_typ t in *)
                (*             AbsynUtils.is_constructor t Const.forall_lid || *)
                (*               AbsynUtils.is_constructor t Const.forallA_lid ||  *)
                (*               AbsynUtils.is_constructor t Const.exists_lid ||  *)
                (*               AbsynUtils.is_constructor t Const.existsA_lid) ->  *)
                (*     (match unascribe_typ t2 with  *)
                (*        | {v=Typ_lam(x, t1, t2); sort=s2} ->  *)
                (*            let binders = AbsynUtils.push_vbinder binders (Some x) in  *)
                (*            let t2, _ = vt () binders t2 in  *)
                (*            let _ = pr "Reached case for %s\n" (Pretty.strTyp t1) in  *)
                (*              twithsort  (Typ_app(twithsort (Typ_app(t, t1)) s1,  *)
                (*                                  twithsort (Typ_lam(x, t1, t2)) s2)) tt.sort, () *)
                (*        | _ -> raise Impos) *)
                | _ -> vt () binders t in
    let re _ _ ve _ binders e = ve () binders e in 
      match t.sort(* .u *) with 
        | Kind_erasable | Kind_prop -> dup_formula t 
        | _ -> fst <| reduce_kte () rk rt re t in 
    
    match destruct env t Const.reln_lid with 
      | Some [Inl arg] -> fst <| project_to_leaves arg
      | _ -> duplicate t
          

    
