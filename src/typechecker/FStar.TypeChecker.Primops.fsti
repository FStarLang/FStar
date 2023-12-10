module FStar.TypeChecker.Primops

(* This module just contains the list of all builtin primitive steps
with their implementations. *)

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Syntax.Syntax

module EMB = FStar.Syntax.Embeddings
module NBE = FStar.TypeChecker.NBETerm

type psc = {
     psc_range : FStar.Compiler.Range.range;
     psc_subst : unit -> subst_t // potentially expensive, so thunked
}

val null_psc : psc
val psc_range : psc -> FStar.Compiler.Range.range
val psc_subst : psc -> subst_t

type interp_t =
    psc -> FStar.Syntax.Embeddings.norm_cb -> universes -> args -> option term
type nbe_interp_t =
    NBE.nbe_cbs -> universes -> NBE.args -> option NBE.t

type primitive_step = {
    name:FStar.Ident.lid;
    arity:int;
    univ_arity:int; // universe arity
    auto_reflect:option int;
    strong_reduction_ok:bool;
    requires_binder_substitution:bool;
    renorm_after:bool; // whether the result of this primop must possibly undergo more normalization
    interpretation:interp_t;
    interpretation_nbe:nbe_interp_t;
}

(* Some helpers for the NBE. Does not really belong in this module. *)
val embed_simple: {| EMB.embedding 'a |} -> Range.range -> 'a -> term
val try_unembed_simple: {| EMB.embedding 'a |} -> term -> option 'a

val built_in_primitive_steps_list
  : list primitive_step
val equality_ops_list
  : list primitive_step
