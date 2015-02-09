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

val free_variables: term -> list<var>

val mkTrue : term
val mkFalse : term
val mkInteger : int -> term
val mkBoundV : (string * sort) -> term
val mkFreeV  : (string * sort) -> term
val mkPP   : (term * term) -> term
val mkApp  : (string * list<term>) -> term
val mkNot  : term -> term
val mkAnd  : (term * term) -> term
val mkOr  : (term * term) -> term
val mkImp : (term * term) -> term
val mkIff : (term * term) -> term
val mkEq : (term * term) -> term
val mkLT : (term * term) -> term
val mkLTE : (term * term) -> term
val mkGT: (term * term) -> term
val mkGTE: (term * term) -> term
val mkAdd: (term * term) -> term
val mkSub: (term * term) -> term
val mkDiv: (term * term) -> term
val mkMul: (term * term) -> term
val mkMinus: term -> term
val mkMod: (term * term) -> term
val mkITE: (term * term * term) -> term 
val mkSelect: (term * term) -> term
val mkUpdate: (term * term * term) -> term 
val mkCases : list<term> -> term
val mkConstArr: (string * sort * term) -> term
val mkForall: (list<pat> * list<(string * sort)> * term) -> term
val mkForall': (list<list<pat>> * option<int> * list<(string * sort)> * term) -> term
val mkExists: (list<pat> * list<(string * sort)> * term) -> term

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

val constructor_to_decl_aux: bool -> constructor_t -> decls_t
val constructor_to_decl: constructor_t -> decls_t
val termToSmt: term -> string
val declToSmt: string -> decl -> string

val mk_Kind_type : term
val mk_Typ_app : term -> term -> term
val mk_Typ_dep : term -> term -> term
val mk_Typ_uvar: int -> term
val mk_and_l: list<term> -> term
val mk_or_l: list<term> -> term

val boxInt: term -> term
val unboxInt: term -> term
val boxBool: term -> term
val unboxBool: term -> term
val boxString: term -> term
val unboxString: term -> term
val boxRef: term -> term
val unboxRef: term -> term

val mk_Closure: int -> list<var> -> term
val mk_Term_unit: term
val mk_PreKind: term -> term
val mk_PreType: term -> term
val mk_Valid: term -> term
val mk_HasType: term -> term -> term
val mk_HasTypeFuel: term -> term -> term -> term
val mk_HasTypeWithFuel: option<term> -> term -> term -> term 
val mk_HasKind: term -> term -> term
val mk_tester: string -> term -> term
val mk_ApplyTE: term -> term -> term
val mk_ApplyTT: term -> term -> term
val mk_ApplyET: term -> term -> term
val mk_ApplyEE: term -> term -> term
val mk_String_const: int -> term
val mk_Precedes: term -> term -> term
val mk_LexCons: term -> term -> term
val freeV_sym: term -> string
val boundV_sym:term -> string
val fuel_2: term
val fuel_100:term
val n_fuel: int -> term