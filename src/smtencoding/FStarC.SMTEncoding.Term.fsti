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
  | BvExtRol
  | BvExtRor
  | BvRol of int
  | BvRor of int
  | BvUext of int
  | BvNot
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
val escape: string -> string

type error_label = (fv & Errors.error_message & Range.t)
type error_labels = list error_label

(*
 * AR: sym_name -> md5 -> auxiliary decls -> decls
 *     the auxilkiary decls are those that are not directly related to
 *       the symbol itself, but must be retained in case of cache hits
 *       for example, decls for argument types in the case of a Tm_arrow
 *)
val mk_decls: string -> string -> list decl -> list decls_elt -> ML decls_t

(*
 * AR: for when we don't hashcons the decls
 *)
val mk_decls_trivial: list decl -> ML decls_t

(*
 * Flatten the decls_t
 *)
val decls_list_of: decls_t -> ML (list decl)

val mk_fv : string & sort -> fv
val fv_name : fv -> string
val fv_sort : fv -> sort
val fv_force : fv -> bool
val fv_eq : fv -> fv -> bool
val fvs_subset_of: fvs -> fvs -> ML bool
val fv_of_term : term -> ML fv
val free_variables: term -> ML fvs
val free_top_level_names : term -> ML (RBSet.t string)
val op_to_string: op -> ML string
val hash_of_term: term -> ML string
val boxIntFun : string & string
val boxBoolFun : string & string
val boxStringFun : string & string
val boxRealFun: string & string
val mk: term' -> Range.t -> ML term
val mkTrue :  (Range.t -> ML term)
val mkFalse : (Range.t -> ML term)
val mkUnreachable : term
val mkInteger : string -> Range.t -> ML term
val mkInteger': int -> Range.t -> ML term
val mkReal: string -> Range.t -> ML term
val mkBoundV : int -> Range.t -> ML term
val mkFreeV  : fv -> Range.t -> ML term
val mkApp' : (op & list term) -> Range.t -> ML term
val mkApp  : (string & list term) -> Range.t -> ML term
val mkNot  : term -> Range.t -> ML term
val mkAnd  : ((term & term) -> Range.t -> ML term)
val mkOr  :  ((term & term) -> Range.t -> ML term)
val mkImp :  ((term & term) -> Range.t -> ML term)
val mkMinus: term -> Range.t -> ML term
val mkNatToBv : (int -> term -> Range.t -> ML term)
val mkBvUext  : (int -> term -> Range.t -> ML term)
val mkBvNot   : (term -> Range.t -> ML term)
val mkBvToNat : (term -> Range.t -> ML term)
val mkBvAnd   : ((term & term) -> Range.t -> ML term)
val mkBvXor   : ((term & term) -> Range.t -> ML term)
val mkBvOr    : ((term & term) -> Range.t -> ML term)
val mkBvAdd   : ((term & term) -> Range.t -> ML term)
val mkBvSub   : ((term & term) -> Range.t -> ML term)
val mkBvShl   : (int -> (term & term) -> Range.t -> ML term)
val mkBvShr   : (int -> (term & term) -> Range.t -> ML term)
val mkBvRol   : (int -> (term & term) -> Range.t -> ML term)
val mkBvRor   : (int -> (term & term) -> Range.t -> ML term)
val mkBvUdiv  : (int -> (term & term) -> Range.t -> ML term)
val mkBvMod   : (int -> (term & term) -> Range.t -> ML term)
val mkBvMul   : (int -> (term & term) -> Range.t -> ML term)
val mkBvShl'  : (int -> (term & term) -> Range.t -> ML term)
val mkBvShr'  : (int -> (term & term) -> Range.t -> ML term)
val mkBvRol'  : (int -> (term & term) -> Range.t -> ML term)
val mkBvRor'  : (int -> (term & term) -> Range.t -> ML term)
val mkBvMul'  : (int -> (term & term) -> Range.t -> ML term)
val mkBvUdivUnsafe : (int -> (term & term) -> Range.t -> ML term)
val mkBvModUnsafe  : (int -> (term & term) -> Range.t -> ML term)
val mkBvUlt   : ((term & term) -> Range.t -> ML term)
val mkIff :  ((term & term) -> Range.t -> ML term)
val mkEq :   ((term & term) -> Range.t -> ML term)
val mkLT :   ((term & term) -> Range.t -> ML term)
val mkLTE :  ((term & term) -> Range.t -> ML term)
val mkGT:    ((term & term) -> Range.t -> ML term)
val mkGTE:   ((term & term) -> Range.t -> ML term)
val mkAdd:   ((term & term) -> Range.t -> ML term)
val mkSub:   ((term & term) -> Range.t -> ML term)
val mkDiv:   ((term & term) -> Range.t -> ML term)
val mkRealDiv:   ((term & term) -> Range.t -> ML term)
val mkMul:   ((term & term) -> Range.t -> ML term)
val mkMod:   ((term & term) -> Range.t -> ML term)
val mkRealOfInt: term -> Range.t -> ML term
val mkITE: (term & term & term) -> Range.t -> ML term
val mkCases : list term -> Range.t -> ML term
val check_pattern_ok: term -> option term
val print_smt_term: term -> ML string
val print_smt_term_list: list term -> ML string
val print_smt_term_list_list: list (list term) -> ML string
val mkLet: (list term & term) -> Range.t -> ML term
val abstr: list fv -> term -> ML term
val inst: list term -> term -> ML term
val subst: term -> fv -> term -> ML term
val mkForall:  Range.t -> (list (list pat) & fvs & term) -> ML term
val mkForall'': Range.t -> (list (list pat) & option int & list sort & term) -> ML term
val mkForall': Range.t -> (list (list pat) & option int & fvs & term)  -> ML term
val mkExists: Range.t -> (list (list pat) & fvs & term) -> ML term
val mkForallFlat:  (fvs & term) -> ML term
val mkLet': (list (fv & term) & term) -> Range.t -> ML term
val fresh_token: (term & fvs & sort) -> int -> ML decl
val fresh_constructor : Range.t -> (string & list sort & sort & int) -> ML decl
//val constructor_to_decl_aux: bool -> constructor_t -> decls_t
val constructor_to_decl: Range.t -> constructor_t -> ML (list decl)
val declToSmt: string -> decl -> ML string
val declToSmt_no_caps: string -> decl -> ML string
val mkBvConstructor: int -> ML (list decl & string & string)

// Thunked, produces a different opaque constant on each call
val mk_Range_const:  unit -> ML term
val univ_sort:       sort
val mk_U_zero:       term
val mk_U_succ:       term -> ML term
val mk_U_max:        term -> term -> ML term
val mk_U_name:       string -> ML term
val mk_U_unif:       term -> ML term
val mk_U_unknown:    term
val mk_Term_type:    term -> ML term
val mk_Term_app : term -> term -> Range.t -> ML term
val mk_Term_uvar: int -> Range.t -> ML term
val mk_Term_unit:    term

val boxInt:      term -> ML term
val unboxInt:    term -> ML term
val boxBool:     term -> ML term
val unboxBool:   term -> ML term
val boxString:   term -> ML term
val unboxString: term -> ML term
val boxReal:      term -> ML term
val unboxReal:    term -> ML term
val boxBitVec:   int -> term -> ML term
val unboxBitVec: int -> term -> ML term

val mk_PreType:      term -> ML term
val mk_Valid:        term -> ML term
val mk_subtype_of_unit: term -> ML term
val mk_HasType:      term -> term -> ML term
val mk_HasTypeZ:     term -> term -> ML term
val mk_IsTotFun:     term -> ML term
val mk_HasTypeFuel:  term -> term -> term -> ML term
val mk_HasTypeWithFuel: option term -> term -> term -> ML term
val mk_NoHoist:      term -> term -> ML term
val mk_tester:       string -> term -> ML term
val mk_ApplyTF:      term -> term -> ML term
val mk_ApplyTT:      term -> term -> Range.t -> ML term
val mk_String_const: string -> Range.t -> ML term
val mk_Precedes_term:term -> term -> term -> term -> term -> term -> Range.t -> ML term
val mk_Precedes:     term -> term -> term -> term -> term -> term -> Range.t -> ML term
val mk_lex_t:        Range.t -> ML term
val mk_LexCons:      term -> term -> term -> Range.t -> ML term
val mk_LexTop:       Range.t -> ML term
val n_fuel: int -> ML term
val mk_and_l: list term -> Range.t -> ML term
val mk_or_l: list term -> Range.t -> ML term
val mk_haseq: univ:term -> term -> ML term
val dummy_sort : sort

instance val showable_sort : showable sort
instance val showable_fv : showable fv
instance val showable_smt_term : Class.Show.showable term
instance val showable_decl : showable decl
instance val showable_decls_elt : showable decls_elt

val names_of_decl (d:decl) : ML (list string)
val decl_to_string_short (d:decl) : ML string
