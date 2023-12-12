module FStar.TypeChecker.Primops.Base
(* This module defines the type of primitive steps and some helpers. *)

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

val as_primitive_step_nbecbs
    (is_strong:bool)
    (* (l, arity, u_arity, f, f_nbe) *)
     : (Ident.lident & int & int & interp_t & nbe_interp_t) -> primitive_step

(* Some helpers for the NBE. Does not really belong in this module. *)
val embed_simple: {| EMB.embedding 'a |} -> Range.range -> 'a -> term
val try_unembed_simple: {| EMB.embedding 'a |} -> term -> option 'a

val mk1 #a #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> r)
  : primitive_step

val mk2 #a #b #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> r)
  : primitive_step

(* Duplication for op_Division / op_Modulus which can prevent reduction. The `f`
already returns something in the option monad, so we add an extra join. *)
val mk2' #a #b #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> option r)
  : primitive_step

val mk3 #a #b #c #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding c |} {| NBE.embedding c |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> c -> r)
  : primitive_step

val mk4 #a #b #c #d #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding c |} {| NBE.embedding c |}
  {| EMB.embedding d |} {| NBE.embedding d |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> c -> d -> r)
  : primitive_step

val mk5 #a #b #c #d #e #r
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding a |}
  {| EMB.embedding b |} {| NBE.embedding b |}
  {| EMB.embedding c |} {| NBE.embedding c |}
  {| EMB.embedding d |} {| NBE.embedding d |}
  {| EMB.embedding e |} {| NBE.embedding e |}
  {| EMB.embedding r |} {| NBE.embedding r |}
  (f : a -> b -> c -> d -> e -> r)
  : primitive_step
