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
  | RealDiv
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
  | Real       of string
  | BoundV     of int
  | FreeV      of fv
  | App        of op  * list<term>
  | Quant      of qop * list<list<pat>> * option<int> * list<sort> * term
  | Let        of list<term> * term
  | Labeled    of term * string * Range.range
  | LblPos     of term * string
and pat  = term
and term = {tm:term'; freevars:Syntax.memo<fvs>; rng:Range.range}
and fv = string * sort * bool
and fvs = list<fv>
val fv_name : fv -> string
val fv_sort : fv -> sort
val fv_force : fv -> bool
val mk_fv : string * sort -> fv

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

(*
 * AR: decls_elt captures a block of "related" decls
 *     For example, for a Tm_refine_<MD5> symbol,
 *       decls_elt will have its DeclFun, typing axioms,
 *       hasEq axiom, interpretation, etc.
 *
 *     This allows the encoding of a module to be "stateless"
 *       in terms of hashconsing -- the encoding may contain
 *       duplicate such blocks
 *
 *     Deduplication happens when giving the decls to Z3
 *       at which point, if the key below -- which is the MD5 string --
 *       matches, the whole block is dropped (see Encode.fs.recover_caching_and_update_env)
 *
 *     Alternative way would have been to do some smt name matching
 *       but that would be sensitive to name strings and hence brittle
 *
 *     Before the declarations are given to Z3, the remaining decls_elt
 *       left after deduplication are just "flattened" (using decls_list_of)
 *
 *     sym_name and key are options for cases when we don't care about hashconsing
 *)
type decls_elt = {
  sym_name:   option<string>;  //name of the main synbol, e.g. Tm_refine_<MD5>
  key:        option<string>;  //the MD5 string
  decls:      list<decl>;      //list of decls, e.g. typing axioms, hasEq, for a Tm_refine
  a_names:    list<string>;    //assumption names that must be kept IF this entry has a cache hit
                               //--used to not filter them when using_facts_from
}

type decls_t = list<decls_elt>

(*
 * AR: sym_name -> md5 -> auxiliary decls -> decls
 *     the auxilkiary decls are those that are not directly related to
 *       the symbol itself, but must be retained in case of cache hits
 *       for example, decls for argument types in the case of a Tm_arrow
 *)
val mk_decls: string -> string -> list<decl> -> list<decls_elt> -> decls_t

(*
 * AR: for when we don't hashcons the decls
 *)
val mk_decls_trivial: list<decl> -> decls_t

(*
 * Flatten the decls_t
 *)
val decls_list_of: decls_t -> list<decl>

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
val boxRealFun: string * string
val fv_eq : fv -> fv -> bool
val fv_of_term : term -> fv
val free_variables: term -> fvs
val mkTrue :  (Range.range -> term)
val mkFalse : (Range.range -> term)
val mkInteger : string -> Range.range -> term
val mkInteger': int -> Range.range -> term
val mkReal: string -> Range.range -> term
val mkRealOfInt: term -> Range.range -> term
val mkBoundV : int -> Range.range -> term
val mkFreeV  : fv -> Range.range -> term
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
val mkRealDiv:   ((term * term) -> Range.range -> term)
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
val fresh_constructor : Range.range -> (string * list<sort> * sort * int) -> decl
//val constructor_to_decl_aux: bool -> constructor_t -> decls_t
val constructor_to_decl: Range.range -> constructor_t -> list<decl>
val mkBvConstructor: int -> list<decl>
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
val boxReal:      term -> term
val unboxReal:    term -> term
val boxBitVec:   int -> term -> term
val unboxBitVec: int -> term -> term

// Thunked, produces a different opaque constant on each call
val mk_Range_const:  unit -> term
val mk_Term_unit:    term

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

val dummy_sort : sort
