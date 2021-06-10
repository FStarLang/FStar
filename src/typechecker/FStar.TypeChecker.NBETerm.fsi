(*
   Copyright 2017-2019 Microsoft Research

   Authors: Zoe Paraskevopoulou, Guido Martinez, Nikhil Swamy

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
module FStar.TypeChecker.NBETerm
open FStar.Pervasives
open FStar.All
open FStar.Exn
open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Errors
open FStar.VConfig

module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module BU = FStar.Util
module Env = FStar.TypeChecker.Env
module Z = FStar.BigInt
module C = FStar.Const
open FStar.Char

(*
   This module provides the internal term representations used in the
   NBE algorithm implemented by FStar.TypeChecker.NBE.fs (see the
   comments at the header of that file, for some general context about
   the algorithm).

   Although the type provided by this module is mostly of relevance to
   the internal of the NBE algorithm, we expose its definitions mainly
   so that we can (in FStar.TypeChecker.Cfg and
   FStar.Tactics.Interpreter) provide NBE compatible implementations
   of primitive computation steps.
*)

type var = bv
type sort = int

// This type mostly mirrors the definition of FStar.Const.sconst
// There are several missing cases, however.
// TODO: We should also provide implementations for float, bytearray,
// etc.
type constant =
  | Unit
  | Bool of bool
  | Int of Z.t
  | String of string * Range.range
  | Char of FStar.Char.char
  | Range of Range.range
  | SConst of FStar.Const.sconst

// Atoms represent the head of an irreducible application
// They can either be variables
// Or, un-reduced match terms
type atom
  =
  | Var of var
  | Match of
       // 1. the scrutinee
       t *
       // 2. reconstruct the returns annotation
       (unit -> option<ascription>) *
       // 3. reconstructs the pattern matching, if it needs to be readback
       (unit -> list<branch>)
  | UnreducedLet of
     // Especially when extracting, we do not always want to reduce let bindings
     // since that can lead to exponential code size blowup. This node represents
     // an unreduced let binding which can be read back as an F* let
     // 1. The name of the let-bound term
       var *
     // 2. The type of the let-bound term
       Thunk.t<t>   *
     // 3. Its definition
       Thunk.t<t>   *
     // 4. The body of the let binding
       Thunk.t<t>   *
     // 5. The source letbinding for readback (of attributes etc.)
       letbinding
  | UnreducedLetRec of
     // Same as UnreducedLet, but for local let recs
     // 1. list of names of all mutually recursive let-rec-bound terms
     //    * their types
     //    * their definitions
        list<(var * t * t)> *
     // 2. the body of the let binding
        t *
     // 3. the source letbinding for readback (of attributes etc.)
     //    equal in length to the first list
        list<letbinding>
  | UVar of Thunk.t<S.term>

and t'
  =
  | Lam of (list<t> -> t)            //these expect their arguments in binder order (optimized for convenience beta reduction)
        * either<(list<t> * binders * option<S.residual_comp>), list<arg>> //a context, binders and residual_comp for readback
                                                                 //or a list of arguments, for primitive unembeddings
        * int                        // arity
  | Accu of atom * args
  | Construct of fv * list<universe> * args
  | FV of fv * list<universe> * args //universes and args in reverse order
  | Constant of constant
  | Type_t of universe
  | Univ of universe
  | Unknown
  | Arrow of either<Thunk.t<S.term>, (list<arg> * comp)>
  | Refinement of (t -> t) * (unit -> arg)
  | Reflect of t
  | Quote of S.term * S.quoteinfo
  | Lazy of either<S.lazyinfo,(Dyn.dyn * emb_typ)> * Thunk.t<t>
  | Meta of t * Thunk.t<S.metadata>
  | TopLevelLet of
       // 1. The definition of the fv
       letbinding *
       // 2. Its natural arity including universes (see Util.let_rec_arity)
       int *
       // 3. Accumulated arguments in order from left-to-right (unlike Accu, these are not reversed)
       args
  | TopLevelRec of
       // 1. The definition of the fv
       letbinding *
       // 2. Its natural arity including universes (see Util.let_rec_arity)
       int *
       // 3. Whether or not each argument appeats in the decreases clause (also see Util.let_rec_arity)
       list<bool> *
       // 4. Accumulated arguments in order from left-to-right (unlike Accu, these are not reversed)
       args
  | LocalLetRec of
      // 1. index of the let binding in the mutually recursive list
      int *
      letbinding *
      // 2. Mutally recursive letbindings (only for local mutually recursive let bindings)
      list<letbinding> *
      // 3. rec env
      list<t> *
      // 4. Argument accumulator
      args *
      // 5. natural arity (including universes) of the main let binding `f` (see Util.let_rec_arity)
      int *
      // 6. for each argument, a bool records if that argument appears in the decreases
      //    This is used to detect potentially non-terminating loops
      list<bool>

and t = {
  nbe_t : t';
  nbe_r : Range.range
}

and comp =
  | Tot of t * option<universe>
  | GTot of t * option<universe>
  | Comp of comp_typ

and comp_typ = {
  comp_univs:universes;
  effect_name:lident;
  result_typ:t;
  effect_args:args;
  flags:list<cflag>
}

and residual_comp = {
  residual_effect:lident;
  residual_typ   :option<t>;
  residual_flags :list<cflag>
}

and cflag =
  | TOTAL
  | MLEFFECT
  | RETURN
  | PARTIAL_RETURN
  | SOMETRIVIAL
  | TRIVIAL_POSTCONDITION
  | SHOULD_NOT_INLINE
  | LEMMA
  | CPS
  | DECREASES_lex of list<t>
  | DECREASES_wf of (t * t)

and arg = t * aqual
and args = list<(arg)>

type head = t
type annot = option<t>

// Printing functions

val constant_to_string : constant -> string
val t_to_string : t -> string
val atom_to_string : atom -> string
val arg_to_string : arg -> string
val args_to_string : args -> string

// NBE term manipulation
val mk_t : t' -> t
val nbe_t_of_t : t -> t'
val isAccu : t -> bool
val isNotAccu : t -> bool

val mkConstruct : fv -> list<universe> -> args -> t
val mkFV : fv -> list<universe> -> args -> t

val mkAccuVar : var -> t
val mkAccuMatch : t -> (unit -> option<ascription>) -> (unit -> list<branch>) -> t

val as_arg : t -> arg
val as_iarg : t -> arg

type nbe_cbs = {
   iapp : t -> args -> t;
   translate : term -> t;
}

val iapp_cb      : nbe_cbs -> t -> args -> t
val translate_cb : nbe_cbs -> term -> t

type embedding<'a> = {
  em  : nbe_cbs -> 'a -> t;
  un  : nbe_cbs -> t -> option<'a>;
  typ : t;
  emb_typ : emb_typ
}

val mk_emb : (nbe_cbs -> 'a -> t) ->
             (nbe_cbs -> t -> option<'a>) ->
             t ->
             emb_typ ->
             embedding<'a>

val embed_as : embedding<'a> -> ('a -> 'b) -> ('b -> 'a) -> option<t> -> embedding<'b>

val embed   : embedding<'a> -> nbe_cbs -> 'a -> t
val unembed : embedding<'a> -> nbe_cbs -> t -> option<'a>
val type_of : embedding<'a> -> t

val e_bool   : embedding<bool>
val e_string : embedding<string>
val e_char   : embedding<char>
val e_int    : embedding<Z.t>
val e_unit   : embedding<unit>
val e_any    : embedding<t>
val mk_any_emb : t -> embedding<t>
val e_range  : embedding<Range.range>
val e_vconfig  : embedding<vconfig>
val e_norm_step : embedding<Syntax.Embeddings.norm_step>
val e_list   : embedding<'a> -> embedding<list<'a>>
val e_option : embedding<'a> -> embedding<option<'a>>
val e_tuple2 : embedding<'a> -> embedding<'b> -> embedding<('a * 'b)>
val e_either : embedding<'a> -> embedding<'b> -> embedding<either<'a ,'b>>
val e_string_list : embedding<list<string>>
val e_arrow : embedding<'a> -> embedding<'b> -> embedding<('a -> 'b)>

(* Arity specific raw_embeddings of arrows; used to generate top-level
   registrations of compiled functions in FStar.Extraction.ML.Util *)
val arrow_as_prim_step_1:  embedding<'a>
                        -> embedding<'b>
                        -> ('a -> 'b)
                        -> n_tvars:int
                        -> repr_f:Ident.lid
                        -> nbe_cbs
                        -> (args -> option<t>)

val arrow_as_prim_step_2:  embedding<'a>
                        -> embedding<'b>
                        -> embedding<'c>
                        -> ('a -> 'b -> 'c)
                        -> n_tvars:int
                        -> repr_f:Ident.lid
                        -> nbe_cbs
                        -> (args -> option<t>)

val arrow_as_prim_step_3:  embedding<'a>
                        -> embedding<'b>
                        -> embedding<'c>
                        -> embedding<'d>
                        -> ('a -> 'b -> 'c -> 'd)
                        -> n_tvars:int
                        -> repr_f:Ident.lid
                        -> nbe_cbs
                        -> (args -> option<t>)



// Interface for NBE interpretations

val arg_as_int : arg -> option<Z.t>
val arg_as_bool : arg -> option<bool>
val arg_as_char : arg -> option<FStar.Char.char>
val arg_as_string : arg -> option<string>
val arg_as_list : embedding<'a> -> arg -> option<list<'a>>
val arg_as_bounded_int : arg -> option<(fv * Z.t)>

val int_as_bounded : fv -> Z.t -> t

val unary_int_op : (Z.t -> Z.t) -> (args -> option<t>)
val binary_int_op : (Z.t -> Z.t -> Z.t) -> (args -> option<t>)

val unary_bool_op : (bool -> bool) -> (args -> option<t>)
val binary_bool_op : (bool -> bool -> bool) -> (args -> option<t>)

val binary_string_op : (string -> string -> string) -> (args -> option<t>)

val string_of_int : Z.t -> t
val string_of_bool : bool -> t
val string_of_list' : list<char> -> t
val string_compare' : string -> string -> t
val string_concat' : args -> option<t>
val string_substring' : args -> option<t>
val string_split' : args -> option<t>
val string_lowercase : string -> t
val string_uppercase : string -> t
val string_index : args -> option<t>
val string_index_of : args -> option<t>

val list_of_string' : (string -> t)

val decidable_eq : bool -> args -> option<t>
val interp_prop_eq2 : args -> option<t>
val interp_prop_eq3 : args -> option<t>

val mixed_binary_op : (arg -> option<'a>) -> (arg -> option<'b>) -> ('c -> t) ->
                      ('a -> 'b -> 'c) -> args -> option<t>
val unary_op : (arg -> option<'a>) -> ('a -> t) -> (args -> option<t>)
val binary_op : (arg -> option<'a>) -> ('a -> 'a -> t) -> (args -> option<t>)

val dummy_interp : Ident.lid -> args -> option<t>
val prims_to_fstar_range_step : args -> option<t>

val mk_range : args -> option<t>
val division_op : args -> option<t>
val and_op : args -> option<t>
val or_op : args -> option<t>
