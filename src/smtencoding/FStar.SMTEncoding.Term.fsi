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

module FStar.SMTEncoding.Term
open Prims
    open FStar
open FStar.Syntax.Syntax
open FStar.Syntax
open FStar.Util

type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Ref_sort
  | Term_sort
  | Fuel_sort
  | Array of sort * sort
  | Arrow of sort * sort
  | Sort of string

type op =
  | TrueOp
  | FalseOp
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
  | Labeled    of term * string * Range.range
  | LblPos     of term * string
and pat  = term
and term = {tm:term'; freevars:Syntax.memo<fvs>; rng:Range.range}
and fv = string * sort
and fvs = list<fv>

type caption = option<string>
type binders = list<(string * sort)>
type projector = (string * sort)
type constructor_t = (string * list<projector> * sort * int * bool)
type constructors  = list<constructor_t>
type decl =
  | DefPrelude
  | DeclFun    of string * list<sort> * sort * caption
  | DefineFun  of string * list<sort> * sort * term * caption
  | Assume     of term   * caption * option<string>
  | Caption    of string
  | Eval       of term
  | Echo       of string
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption  of string * string
  | PrintStats
type decls_t = list<decl>

type error_label = (fv * string * Range.range)
type error_labels = list<error_label>

val abstr: list<fv> -> term -> term
val inst: list<term> -> term -> term
val mk: term' -> Range.range -> term
val hash_of_term: term -> string
val fv_eq : fv -> fv -> bool
val fv_of_term : term -> fv
val free_variables: term -> fvs
val mkTrue :  (Range.range -> term)
val mkFalse : (Range.range -> term)
val mkInteger : string -> Range.range -> term
val mkInteger': int -> Range.range -> term
val mkBoundV : int -> Range.range -> term
val mkFreeV  : (string * sort) -> Range.range -> term
val mkApp' : (op * list<term>) -> Range.range -> term
val mkApp  : (string * list<term>) -> Range.range -> term
val mkNot  : term -> Range.range -> term
val mkMinus: term -> Range.range -> term
val mkAnd  : ((term * term) -> Range.range -> term)
val mkOr  :  ((term * term) -> Range.range -> term)
val mkImp :  ((term * term) -> Range.range -> term)
val mkIff :  ((term * term) -> Range.range -> term)
val mkEq :   ((term * term) -> Range.range -> term)
val mkLT :   ((term * term) -> Range.range -> term)
val mkLTE :  ((term * term) -> Range.range -> term)
val mkGT:    ((term * term) -> Range.range -> term)
val mkGTE:   ((term * term) -> Range.range -> term)
val mkAdd:   ((term * term) -> Range.range -> term)
val mkSub:   ((term * term) -> Range.range -> term)
val mkDiv:   ((term * term) -> Range.range -> term)
val mkMul:   ((term * term) -> Range.range -> term)
val mkMod:   ((term * term) -> Range.range -> term)
val mkITE: (term * term * term) -> Range.range -> term
val mkCases : list<term> -> Range.range -> term
val mkForall: (list<list<pat>> * fvs * term) -> Range.range -> term
val mkForall': (list<list<pat>> * option<int> * fvs * term) -> Range.range -> term
val mkForall'': (list<list<pat>> * option<int> * list<sort> * term) -> Range.range -> term
val mkExists: (list<list<pat>> * fvs * term) -> Range.range -> term

val fresh_token: (string * sort) -> int -> decl
val injective_constructor : (string * list<(string * sort)> * sort) -> decls_t
val fresh_constructor : (string * list<sort> * sort * int) -> decl
//val constructor_to_decl_aux: bool -> constructor_t -> decls_t
val constructor_to_decl: constructor_t -> decls_t
val termToSmt: term -> string
val declToSmt: string -> decl -> string

val mk_Term_app : term -> term -> Range.range -> term
val mk_Term_uvar: int -> Range.range -> term
val mk_and_l: list<term> -> Range.range -> term
val mk_or_l: list<term> -> Range.range -> term

val boxInt:      term -> term
val unboxInt:    term -> term
val boxBool:     term -> term
val unboxBool:   term -> term
val boxString:   term -> term
val unboxString: term -> term
val boxRef:      term -> term
val unboxRef:    term -> term

val mk_Range_const:  term
val mk_Term_unit:    term

val mk_PreType:      term -> term
val mk_Valid:        term -> term
val mk_HasType:      term -> term -> term
val mk_HasTypeZ:     term -> term -> term
val mk_IsTyped:      term -> term
val mk_HasTypeFuel:  term -> term -> term -> term
val mk_HasTypeWithFuel: option<term> -> term -> term -> term
val mk_tester:       string -> term -> term
val mk_Term_type:    term
val mk_ApplyTF:      term -> term -> term
val mk_ApplyTT:      term -> term -> Range.range -> term
val mk_String_const: int -> Range.range -> term
val mk_Precedes:     term -> term -> Range.range -> term
val mk_LexCons:      term -> term -> Range.range -> term
val fuel_2: term
val fuel_100:term
val n_fuel: int -> term

val mk_haseq: term -> term

val print_smt_term: term -> string
val print_smt_term_list: list<term> -> string
val print_smt_term_list_list: list<list<term>> -> string

