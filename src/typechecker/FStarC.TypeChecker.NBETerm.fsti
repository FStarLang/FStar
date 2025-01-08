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

module FStarC.TypeChecker.NBETerm

open FStar open FStarC
open FStarC.Compiler
open FStarC.Compiler.Effect
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.VConfig
open FStar.Char

module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module Z = FStarC.BigInt
module TEQ = FStarC.TypeChecker.TermEqAndSimplify
open FStarC.Class.Show

val interleave_hack : int

(*
   This module provides the internal term representations used in the
   NBE algorithm implemented by FStarC.TypeChecker.NBE.fs (see the
   comments at the header of that file, for some general context about
   the algorithm).

   Although the type provided by this module is mostly of relevance to
   the internal of the NBE algorithm, we expose its definitions mainly
   so that we can (in FStarC.TypeChecker.Cfg and
   FStarC.Tactics.Interpreter) provide NBE compatible implementations
   of primitive computation steps.
*)

type var = bv
type sort = int

// This type mostly mirrors the definition of FStarC.Const.sconst
// There are several missing cases, however.
// TODO: We should also provide implementations for float, bytearray,
// etc.
type constant =
  | Unit
  | Bool of bool
  | Int of Z.t
  | String of string & Range.range
  | Char of FStar.Char.char
  | Range of Range.range
  | SConst of FStarC.Const.sconst
  | Real of string

// Atoms represent the head of an irreducible application
// They can either be variables
// Or, un-reduced match terms
type atom
  =
  | Var of var
  | Match of
       // 1. the scrutinee
       t &
       // 2. reconstruct the returns annotation
       (unit -> option match_returns_ascription) &
       // 3. reconstructs the pattern matching, if it needs to be readback
       (unit -> list branch) &
       // 4. reconstruct the residual comp if set
       (unit -> option S.residual_comp)
  | UnreducedLet of
     // Especially when extracting, we do not always want to reduce let bindings
     // since that can lead to exponential code size blowup. This node represents
     // an unreduced let binding which can be read back as an F* let
     // 1. The name of the let-bound term
       var &
     // 2. The type of the let-bound term
       Thunk.t t   &
     // 3. Its definition
       Thunk.t t   &
     // 4. The body of the let binding
       Thunk.t t   &
     // 5. The source letbinding for readback (of attributes etc.)
       letbinding
  | UnreducedLetRec of
     // Same as UnreducedLet, but for local let recs
     // 1. list of names of all mutually recursive let-rec-bound terms
     //    * their types
     //    * their definitions
        list (var & t & t) &
     // 2. the body of the let binding
        t &
     // 3. the source letbinding for readback (of attributes etc.)
     //    equal in length to the first list
        list letbinding
  | UVar of Thunk.t S.term

and lam_shape =
  // a context, binders and residual_comp for readback
  | Lam_bs of (list t & binders & option S.residual_comp)

  // or a list of arguments, for primitive unembeddings (see e_arrow)
  | Lam_args of (list arg)

  // or a partially applied primop
  | Lam_primop of (S.fv & list arg)

and t' =
  | Lam {
    interp : list (t & aqual) -> t;
    //these expect their arguments in binder order (optimized for convenience beta reduction)
    //we also maintain aquals so as to reconstruct the application properly for implicits

    shape : lam_shape;
    arity : int;
  }

  | Accu of atom & args
  | Construct of fv & list universe & args
  | FV of fv & list universe & args //universes and args in reverse order
  | Constant of constant
  | Type_t of universe
  | Univ of universe
  | Unknown
  | Arrow of either (Thunk.t S.term) (list arg & comp)
  | Refinement of (t -> t) & (unit -> arg)
  | Reflect of t
  | Quote of S.term & S.quoteinfo
  | Lazy of (either S.lazyinfo (Dyn.dyn & emb_typ)) & Thunk.t t
  | Meta of t & Thunk.t S.metadata
  | TopLevelLet of
       // 1. The definition of the fv
       letbinding &
       // 2. Its natural arity including universes (see Util.let_rec_arity)
       int &
       // 3. Accumulated arguments in order from left-to-right (unlike Accu, these are not reversed)
       args
  | TopLevelRec of
       // 1. The definition of the fv
       letbinding &
       // 2. Its natural arity including universes (see Util.let_rec_arity)
       int &
       // 3. Whether or not each argument appeats in the decreases clause (also see Util.let_rec_arity)
       list bool &
       // 4. Accumulated arguments in order from left-to-right (unlike Accu, these are not reversed)
       args
  | LocalLetRec of
      // 1. index of the let binding in the mutually recursive list
      int &
      letbinding &
      // 2. Mutally recursive letbindings (only for local mutually recursive let bindings)
      list letbinding &
      // 3. rec env
      list t &
      // 4. Argument accumulator
      args &
      // 5. natural arity (including universes) of the main let binding `f` (see Util.let_rec_arity)
      int &
      // 6. for each argument, a bool records if that argument appears in the decreases
      //    This is used to detect potentially non-terminating loops
      list bool

and t = {
  nbe_t : t';
  nbe_r : Range.range
}

and comp =
  | Tot of t
  | GTot of t
  | Comp of comp_typ

and comp_typ = {
  comp_univs:universes;
  effect_name:lident;
  result_typ:t;
  effect_args:args;
  flags:list cflag
}

and residual_comp = {
  residual_effect:lident;
  residual_typ   :option t;
  residual_flags :list cflag
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
  | DECREASES_lex of list t
  | DECREASES_wf of (t & t)

and arg = t & aqual
and args = list (arg)

instance val showable_t    : showable t
instance val showable_args : showable args

val isAccu : t -> bool
val isNotAccu : t -> bool

val mkConstruct : fv -> list universe -> args -> t
val mkFV : fv -> list universe -> args -> t

val mkAccuVar : var -> t
val mkAccuMatch : t -> (unit -> option match_returns_ascription) -> (unit -> list branch) -> (unit -> option S.residual_comp) -> t

type head = t
type annot = option t

type nbe_cbs = {
   iapp : t -> args -> t;
   translate : term -> t;
}

class embedding (a:Type0) = {
  em  : nbe_cbs -> a -> t;
  un  : nbe_cbs -> t -> option a;
  (* thunking to allow total instances *)
  typ : unit -> t;
  e_typ : unit -> emb_typ;
}

val eq_t : Env.env_t -> t -> t -> TEQ.eq_result

// Printing functions

val constant_to_string : constant -> string
val t_to_string : t -> string
val atom_to_string : atom -> string
val arg_to_string : arg -> string
val args_to_string : args -> string

// NBE term manipulation
val mk_t : t' -> t
val nbe_t_of_t : t -> t'

val as_arg : t -> arg
val as_iarg : t -> arg

val iapp_cb      : nbe_cbs -> t -> args -> t
val translate_cb : nbe_cbs -> term -> t

val mk_emb : (nbe_cbs -> 'a -> t) ->
             (nbe_cbs -> t -> option 'a) ->
             (unit -> t) ->
             (unit -> emb_typ) ->
             Prims.Tot (embedding 'a)

val embed_as : embedding 'a -> ('a -> 'b) -> ('b -> 'a) -> option t -> embedding 'b

val embed   : embedding 'a -> nbe_cbs -> 'a -> t
val unembed : embedding 'a -> nbe_cbs -> t -> option 'a
val lazy_unembed_lazy_kind (#a:Type) (k:lazy_kind) (x:t) : option a
val type_of : embedding 'a -> t
val set_type : t -> embedding 'a -> embedding 'a

type abstract_nbe_term = | AbstractNBE : t:t -> abstract_nbe_term

instance val e_bool   : embedding bool
instance val e_string : embedding string
instance val e_char   : embedding char
instance val e_int    : embedding Z.t
instance val e_real   : embedding Compiler.Real.real
instance val e_unit   : embedding unit
val e_any    : embedding t
val mk_any_emb : t -> embedding t
val e___range  : embedding Range.range (* unsealed *)
instance val e_range  : embedding Range.range (* sealed *)
instance val e_issue  : embedding FStarC.Errors.issue
instance val e_document : embedding FStarC.Pprint.document
instance val e_vconfig  : embedding vconfig
instance val e_norm_step : embedding Pervasives.norm_step
instance val e_list   : #a:Type -> embedding a -> Prims.Tot (embedding (list a))
instance val e_option : embedding 'a -> Prims.Tot (embedding (option 'a))
instance val e_tuple2 : embedding 'a -> embedding 'b -> Prims.Tot (embedding ('a & 'b))
instance val e_tuple3 : embedding 'a -> embedding 'b -> embedding 'c -> Prims.Tot (embedding ('a & 'b & 'c))
instance val e_tuple4 : embedding 'a -> embedding 'b -> embedding 'c -> embedding 'd -> Prims.Tot (embedding ('a & 'b & 'c & 'd))
instance val e_tuple5 : embedding 'a -> embedding 'b -> embedding 'c -> embedding 'd -> embedding 'e -> Prims.Tot (embedding ('a & 'b & 'c & 'd & 'e))
instance val e_either : embedding 'a -> embedding 'b -> Prims.Tot (embedding (either 'a 'b))
instance val e_sealed : embedding 'a -> Prims.Tot (embedding (FStarC.Compiler.Sealed.sealed 'a))
instance val e_string_list : embedding (list string)
val e_arrow : embedding 'a -> embedding 'b -> embedding ('a -> 'b)

instance val e_abstract_nbe_term : embedding abstract_nbe_term
instance val e_order : embedding FStarC.Compiler.Order.order

(* Unconditionally fails raising an exception when called *)
val e_unsupported : #a:Type -> embedding a

(* Arity specific raw_embeddings of arrows; used to generate top-level
   registrations of compiled functions in FStarC.Extraction.ML.Util *)
val arrow_as_prim_step_1:  embedding 'a
                        -> embedding 'b
                        -> ('a -> 'b)
                        -> repr_f:Ident.lid
                        -> nbe_cbs
                        -> (universes -> args -> option t)

val arrow_as_prim_step_2:  embedding 'a
                        -> embedding 'b
                        -> embedding 'c
                        -> ('a -> 'b -> 'c)
                        -> repr_f:Ident.lid
                        -> nbe_cbs
                        -> (universes -> args -> option t)

val arrow_as_prim_step_3:  embedding 'a
                        -> embedding 'b
                        -> embedding 'c
                        -> embedding 'd
                        -> ('a -> 'b -> 'c -> 'd)
                        -> repr_f:Ident.lid
                        -> nbe_cbs
                        -> (universes -> args -> option t)

// Interface for NBE interpretations

val arg_as_int : arg -> option Z.t
val arg_as_list : embedding 'a -> arg -> option (list 'a)

val mixed_binary_op : (arg -> option 'a) -> (arg -> option 'b) -> ('c -> t) ->
                      (universes -> 'a -> 'b -> option 'c) -> universes -> args -> option t

val mixed_ternary_op (as_a : arg -> option 'a)
                     (as_b : arg -> option 'b)
                     (as_c : arg -> option 'c)                     
                     (embed_d : 'd -> t) 
                     (f : universes -> 'a -> 'b -> 'c -> option 'd)
                     (us:universes)
                     (args : args) : option t

val dummy_interp : Ident.lid -> args -> option t

val and_op : args -> option t
val or_op : args -> option t
