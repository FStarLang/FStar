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
open FStar.ST
open FStar.All
open Prims
    open FStar
open FStar.Syntax.Syntax
open FStar.Syntax
open FStar.Util

type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Term_sort
  | Fuel_sort
  | BitVec_sort of int
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
  | BvAnd
  | BvXor
  | BvOr
  | BvAdd
  | BvSub
  | BvShl
  | BvShr
  | BvUdiv
  | BvMod
  | BvMul
  | BvUlt
  | BvUext of int
  | NatToBv of int
  | BvToNat
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
  | Let        of list<term> * term
  | Labeled    of term * string * Range.range
  | LblPos     of term * string
and pat  = term
and term = {tm:term'; freevars:Syntax.memo<fvs>; rng:Range.range}
and fv = string * sort
and fvs = list<fv>

type caption = option<string>
type binders = list<(string * sort)>
type constructor_field = string  //name of the field
                       * sort    //sort of the field
                       * bool    //true if the field is projectible
type constructor_t = (string * list<constructor_field> * sort * int * bool)
type constructors  = list<constructor_t>
type fact_db_id =
    | Name of Ident.lid
    | Namespace of Ident.lid
    | Tag of string
type assumption = {
    assumption_term: term;
    assumption_caption: caption;
    assumption_name: string;
    assumption_fact_ids:list<fact_db_id>
}
type decl =
  | DefPrelude
  | DeclFun    of string * list<sort> * sort * caption
  | DefineFun  of string * list<sort> * sort * term * caption
  | Assume     of assumption
  | Caption    of string
  | Module     of string * list<decl>
  | Eval       of term
  | Echo       of string
  | RetainAssumptions of list<string>
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption  of string * string
  | GetStatistics
  | GetReasonUnknown
type decls_t = list<decl>

type error_label = (fv * string * Range.range)
type error_labels = list<error_label>

val escape: string -> string
val abstr: list<fv> -> term -> term
val inst: list<term> -> term -> term
val subst: term -> fv -> term -> term
val mk: term' -> Range.range -> term
val hash_of_term: term -> string
val boxIntFun : string * string
val boxBoolFun : string * string
val boxStringFun : string * string
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
val mkNatToBv : (int -> term -> Range.range -> term)
val mkBvToNat : (term -> Range.range -> term)
val mkBvAnd   : ((term * term) -> Range.range -> term)
val mkBvXor   : ((term * term) -> Range.range -> term)
val mkBvOr    : ((term * term) -> Range.range -> term)
val mkBvAdd   : ((term * term) -> Range.range -> term)
val mkBvSub   : ((term * term) -> Range.range -> term)
val mkBvUlt   : ((term * term) -> Range.range -> term)
val mkBvUext  : (int -> term -> Range.range -> term)
val mkBvShl   : (int -> (term * term) -> Range.range -> term)
val mkBvShr   : (int -> (term * term) -> Range.range -> term)
val mkBvUdiv  : (int -> (term * term) -> Range.range -> term)
val mkBvMod   : (int -> (term * term) -> Range.range -> term)
val mkBvMul   : (int -> (term * term) -> Range.range -> term)

val mkITE: (term * term * term) -> Range.range -> term
val mkCases : list<term> -> Range.range -> term
val check_pattern_ok: term -> option<term>
val mkForall:  Range.range -> (list<list<pat>> * fvs * term) -> term
val mkForall': Range.range -> (list<list<pat>> * option<int> * fvs * term)  -> term
val mkForall'': Range.range -> (list<list<pat>> * option<int> * list<sort> * term) -> term
val mkExists: Range.range -> (list<list<pat>> * fvs * term) -> term
val mkLet: (list<term> * term) -> Range.range -> term
val mkLet': (list<(fv * term)> * term) -> Range.range -> term

val fresh_token: (string * sort) -> int -> decl
val mkDefineFun: (string * list<(string * sort)> * sort * term * caption) -> decl
val injective_constructor : Range.range -> (string * list<constructor_field> * sort) -> decls_t
val fresh_constructor : Range.range -> (string * list<sort> * sort * int) -> decl
//val constructor_to_decl_aux: bool -> constructor_t -> decls_t
val constructor_to_decl: Range.range -> constructor_t -> decls_t
val mkBvConstructor: int -> decls_t
val declToSmt: string -> decl -> string
val declToSmt_no_caps: string -> decl -> string

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
val boxBitVec:   int -> term -> term
val unboxBitVec: int -> term -> term

// Thunked, produces a different opaque constant on each call
val mk_Range_const:  unit -> term
val mk_Term_unit:    term
val mk_Witness_term:  term

val mk_PreType:      term -> term
val mk_Valid:        term -> term
val mk_HasType:      term -> term -> term
val mk_HasTypeZ:     term -> term -> term
val mk_IsTyped:      term -> term
val mk_HasTypeFuel:  term -> term -> term -> term
val mk_HasTypeWithFuel: option<term> -> term -> term -> term
val mk_NoHoist:      term -> term -> term
val mk_tester:       string -> term -> term
val mk_Term_type:    term
val mk_ApplyTF:      term -> term -> term
val mk_ApplyTT:      term -> term -> Range.range -> term
val mk_String_const: int -> Range.range -> term
val mk_Precedes:     term -> term -> term -> term -> Range.range -> term
val mk_LexCons:      term -> term -> term -> Range.range -> term
val fuel_2: term
val fuel_100:term
val n_fuel: int -> term

val mk_haseq: term -> term
val kick_partial_app: term -> term

val op_to_string: op -> string
val print_smt_term: term -> string
val print_smt_term_list: list<term> -> string
val print_smt_term_list_list: list<list<term>> -> string
