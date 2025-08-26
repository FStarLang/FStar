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

module FStarC.SMTEncoding.Term
open FStarC

open FStarC
open FStarC.Effect
open FStarC.Class.Show
open FStarC.List
open FStarC.Class.Ord

module S = FStarC.Syntax.Syntax

type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Term_sort
  | Fuel_sort
  | BitVec_sort of int
  | Array of sort & sort
  | Arrow of sort & sort
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
  | String     of string
  | Real       of string
  | BoundV     of int
  | FreeV      of fv
  | App        of op  & list term
  | Quant      of qop & list (list pat) & option int & list sort & term
  | Let        of list term & term
  | Labeled    of term & Errors.error_message & Range.t
and pat  = term
and term = {tm:term'; freevars:S.memo fvs; rng:Range.t}
and fv = | FV of string & sort & bool (* bool iff variable must be forced/unthunked *)
and fvs = list fv

type caption = option string
type binders = list (string & sort)
type constructor_field = {
  field_name:string;  //name of the field
  field_sort:sort;    //sort of the field
  field_projectible:bool//true if the field is projectible
}
type constructor_t = {
  constr_name:string;
  constr_fields:list constructor_field;
  constr_sort:sort;
  constr_id:option int;
    //Some i, if a term whose head is this constructor is distinct from 
    //terms with other head constructors
  constr_base: bool; //generate a base to eliminate non-injective arguments
}
type constructors  = list constructor_t
type fact_db_id =
    | Name of Ident.lid
    | Namespace of Ident.lid
    | Tag of string
type assumption = {
    assumption_term: term;
    assumption_caption: caption;
    assumption_name: string;
    assumption_fact_ids:list fact_db_id;
    assumption_free_names: RBSet.t string;
}
type decl =
  | DefPrelude
  | DeclFun    of string & list sort & sort & caption
  | DefineFun  of string & list sort & sort & term & caption
  | Assume     of assumption
  | Caption    of string
  | Module     of string & list decl
  | Eval       of term
  | Echo       of string
  | RetainAssumptions of list string
  | Push       of int
  | Pop        of int
  | CheckSat
  | GetUnsatCore
  | SetOption  of string & string
  | GetStatistics
  | GetReasonUnknown
  | EmptyLine

(*
 * AR: decls_elt captures a block of "related" decls
 *     For example, for a Tm_refine_ MD5 symbol,
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
  sym_name:   option string;  //name of the main synbol, e.g. Tm_refine_ MD5
  key:        option string;  //the MD5 string
  decls:      list decl;      //list of decls, e.g. typing axioms, hasEq, for a Tm_refine
  a_names:    list string;    //assumption names that must be kept IF this entry has a cache hit
                               //--used to not filter them when using_facts_from
}

type decls_t = list decls_elt

val fv_name : fv -> string
val fv_sort : fv -> sort
val fv_force : fv -> bool
val mk_fv : string & sort -> fv


(*
 * AR: sym_name -> md5 -> auxiliary decls -> decls
 *     the auxilkiary decls are those that are not directly related to
 *       the symbol itself, but must be retained in case of cache hits
 *       for example, decls for argument types in the case of a Tm_arrow
 *)
val mk_decls: string -> string -> list decl -> list decls_elt -> decls_t

(*
 * AR: for when we don't hashcons the decls
 *)
val mk_decls_trivial: list decl -> decls_t

(*
 * Flatten the decls_t
 *)
val decls_list_of: decls_t -> list decl

type error_label = (fv & Errors.error_message & Range.t)
type error_labels = list error_label

val escape: string -> string
val abstr: list fv -> term -> term
val inst: list term -> term -> term
val subst: term -> fv -> term -> term
val mk: term' -> Range.t -> term
val hash_of_term: term -> string
val boxIntFun : string & string
val boxBoolFun : string & string
val boxStringFun : string & string
val boxRealFun: string & string
val fv_eq : fv -> fv -> bool
val fv_of_term : term -> fv
val fvs_subset_of: fvs -> fvs -> bool
val free_variables: term -> fvs
val free_top_level_names : term -> RBSet.t string
val mkTrue :  (Range.t -> term)
val mkFalse : (Range.t -> term)
val mkUnreachable : term
val mkInteger : string -> Range.t -> term
val mkInteger': int -> Range.t -> term
val mkReal: string -> Range.t -> term
val mkRealOfInt: term -> Range.t -> term
val mkBoundV : int -> Range.t -> term
val mkFreeV  : fv -> Range.t -> term
val mkApp' : (op & list term) -> Range.t -> term
val mkApp  : (string & list term) -> Range.t -> term
val mkNot  : term -> Range.t -> term
val mkMinus: term -> Range.t -> term
val mkAnd  : ((term & term) -> Range.t -> term)
val mkOr  :  ((term & term) -> Range.t -> term)
val mkImp :  ((term & term) -> Range.t -> term)
val mkIff :  ((term & term) -> Range.t -> term)
val mkEq :   ((term & term) -> Range.t -> term)
val mkLT :   ((term & term) -> Range.t -> term)
val mkLTE :  ((term & term) -> Range.t -> term)
val mkGT:    ((term & term) -> Range.t -> term)
val mkGTE:   ((term & term) -> Range.t -> term)
val mkAdd:   ((term & term) -> Range.t -> term)
val mkSub:   ((term & term) -> Range.t -> term)
val mkDiv:   ((term & term) -> Range.t -> term)
val mkRealDiv:   ((term & term) -> Range.t -> term)
val mkMul:   ((term & term) -> Range.t -> term)
val mkMod:   ((term & term) -> Range.t -> term)
val mkNatToBv : (int -> term -> Range.t -> term)
val mkBvToNat : (term -> Range.t -> term)
val mkBvAnd   : ((term & term) -> Range.t -> term)
val mkBvXor   : ((term & term) -> Range.t -> term)
val mkBvOr    : ((term & term) -> Range.t -> term)
val mkBvAdd   : ((term & term) -> Range.t -> term)
val mkBvSub   : ((term & term) -> Range.t -> term)
val mkBvUlt   : ((term & term) -> Range.t -> term)
val mkBvUext  : (int -> term -> Range.t -> term)
val mkBvShl   : (int -> (term & term) -> Range.t -> term)
val mkBvShr   : (int -> (term & term) -> Range.t -> term)
val mkBvUdiv  : (int -> (term & term) -> Range.t -> term)
val mkBvMod   : (int -> (term & term) -> Range.t -> term)
val mkBvMul   : (int -> (term & term) -> Range.t -> term)
val mkBvShl'  : (int -> (term & term) -> Range.t -> term)
val mkBvShr'  : (int -> (term & term) -> Range.t -> term)
val mkBvUdivUnsafe : (int -> (term & term) -> Range.t -> term)
val mkBvModUnsafe  : (int -> (term & term) -> Range.t -> term)
val mkBvMul'  : (int -> (term & term) -> Range.t -> term)

val mkITE: (term & term & term) -> Range.t -> term
val mkCases : list term -> Range.t -> term
val check_pattern_ok: term -> option term
val mkForall:  Range.t -> (list (list pat) & fvs & term) -> term
val mkForall': Range.t -> (list (list pat) & option int & fvs & term)  -> term
val mkForall'': Range.t -> (list (list pat) & option int & list sort & term) -> term
val mkExists: Range.t -> (list (list pat) & fvs & term) -> term
val mkLet: (list term & term) -> Range.t -> term
val mkLet': (list (fv & term) & term) -> Range.t -> term

val fresh_token: (string & sort) -> int -> decl
val fresh_constructor : Range.t -> (string & list sort & sort & int) -> decl
//val constructor_to_decl_aux: bool -> constructor_t -> decls_t
val constructor_to_decl: Range.t -> constructor_t -> list decl
val mkBvConstructor: int -> list decl & string & string
val declToSmt: string -> decl -> string
val declToSmt_no_caps: string -> decl -> string

val mk_Term_app : term -> term -> Range.t -> term
val mk_Term_uvar: int -> Range.t -> term
val mk_and_l: list term -> Range.t -> term
val mk_or_l: list term -> Range.t -> term

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
val mk_subtype_of_unit: term -> term
val mk_HasType:      term -> term -> term
val mk_HasTypeZ:     term -> term -> term
val mk_IsTotFun:     term -> term
val mk_HasTypeFuel:  term -> term -> term -> term
val mk_HasTypeWithFuel: option term -> term -> term -> term
val mk_NoHoist:      term -> term -> term
val mk_tester:       string -> term -> term
val mk_Term_type:    term
val mk_ApplyTF:      term -> term -> term
val mk_ApplyTT:      term -> term -> Range.t -> term
val mk_String_const: string -> Range.t -> term
val mk_Precedes:     term -> term -> term -> term -> Range.t -> term
val n_fuel: int -> term

val mk_haseq: term -> term
val kick_partial_app: term -> term

val op_to_string: op -> string
val print_smt_term: term -> string
val print_smt_term_list: list term -> string
val print_smt_term_list_list: list (list term) -> string

val dummy_sort : sort

instance val showable_smt_term : Class.Show.showable term
instance val showable_decl : showable decl
val names_of_decl (d:decl) : list string
val decl_to_string_short (d:decl) : string
