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
  | Var of string

type qop =
  | Forall
  | Exists

type term' =
  | Integer    of string
  | BoundV     of int
  | FreeV      of fv
  | App        of op  * list<term>
  | Quant      of qop * list<list<pat>> * option<int> * list<sort> * term
and pat  = term
and term = {tm:term'; hash:string; freevars:Syntax.memo<fvs>}
and fv = string * sort
and fvs = list<fv>

val fv_eq : fv -> fv -> bool
val fv_of_term : term -> fv
val free_variables: term -> fvs
val mkTrue : term
val mkFalse : term
val mkInteger : string -> term
val mkInteger32 : int32 -> term
val mkInteger': int -> term
val mkBoundV : int -> term
val mkFreeV  : (string * sort) -> term
val mkApp' : (op * list<term>) -> term
val mkApp  : (string * list<term>) -> term
val mkNot  : term -> term
val mkMinus: term -> term
val mkAnd  : ((term * term) -> term)
val mkOr  :  ((term * term) -> term)
val mkImp :  ((term * term) -> term)
val mkIff :  ((term * term) -> term)
val mkEq :   ((term * term) -> term)
val mkLT :   ((term * term) -> term)
val mkLTE :  ((term * term) -> term)
val mkGT:    ((term * term) -> term)
val mkGTE:   ((term * term) -> term)
val mkAdd:   ((term * term) -> term)
val mkSub:   ((term * term) -> term)
val mkDiv:   ((term * term) -> term)
val mkMul:   ((term * term) -> term)
val mkMod:   ((term * term) -> term)
val mkITE: (term * term * term) -> term
val mkCases : list<term> -> term
val mkForall: (list<list<pat>> * fvs * term) -> term
val mkForall': (list<list<pat>> * option<int> * fvs * term) -> term
val mkForall'': (list<list<pat>> * option<int> * list<sort> * term) -> term
val mkExists: (list<list<pat>> * fvs * term) -> term

type caption = option<string>
type binders = list<(string * sort)>
type projector = (string * sort)
type constructor_t = (string * list<projector> * sort * int)
type constructors  = list<constructor_t>
type decl =
  | DefPrelude
  | DeclFun    of string * list<sort> * sort * caption
  | DefineFun  of string * list<sort> * sort * term * caption
  | Assume     of term   * caption
  | Caption    of string
  | Eval       of term
  | Echo       of string
  | Push
  | Pop
  | CheckSat
type decls_t = list<decl>

val fresh_token: (string * sort) -> int -> decl
//val constructor_to_decl_aux: bool -> constructor_t -> decls_t
val constructor_to_decl: constructor_t -> decls_t
val termToSmt: term -> string
val declToSmt: string -> decl -> string

val mk_Kind_type : term
val mk_Kind_uvar : int -> term
val mk_Typ_app : term -> term -> term
val mk_Typ_dep : term -> term -> term
val mk_Typ_uvar: int -> term
val mk_Exp_uvar: int -> term
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

val mk_Term_unit: term
val mk_PreKind: term -> term
val mk_PreType: term -> term
val mk_Valid: term -> term
val mk_HasType: term -> term -> term
val mk_HasTypeZ: term -> term -> term
val mk_IsTyped: term -> term
val mk_HasTypeFuel: term -> term -> term -> term
val mk_HasTypeWithFuel: option<term> -> term -> term -> term
val mk_HasKind: term -> term -> term
val mk_tester: string -> term -> term
val mk_ApplyTE: term -> term -> term
val mk_ApplyTT: term -> term -> term
val mk_ApplyET: term -> term -> term
val mk_ApplyEE: term -> term -> term
val mk_ApplyEF: term -> term -> term
val mk_String_const: int -> term
val mk_Precedes: term -> term -> term
val mk_LexCons: term -> term -> term
val fuel_2: term
val fuel_100:term
val n_fuel: int -> term

val print_smt_term: term -> string
val print_smt_term_list: list<term> -> string
val print_smt_term_list_list: list<list<term>> -> string

