module FStarC.TypeChecker.Primops.Base
(* This module defines the type of primitive steps and some helpers. *)

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Syntax.Syntax
module EMB = FStarC.Syntax.Embeddings
module NBE = FStarC.TypeChecker.NBETerm

type psc = {
     psc_range : FStarC.Range.range;
     psc_subst : unit -> subst_t // potentially expensive, so thunked
}

val null_psc : psc
val psc_range : psc -> FStarC.Range.range
val psc_subst : psc -> subst_t

type interp_t =
    psc -> FStarC.Syntax.Embeddings.norm_cb -> universes -> args -> option term
type nbe_interp_t =
    NBE.nbe_cbs -> universes -> NBE.args -> option NBE.t

type primitive_step = {
    name:FStarC.Ident.lid;
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

val mk_interp1 #a #r
  {| EMB.embedding a |}
  {| EMB.embedding r |}
  (f : a -> r)
  : interp_t

val mk_nbe_interp1 #a #r
  {| NBE.embedding a |}
  {| NBE.embedding r |}
  (f : a -> r)
  : nbe_interp_t

val mk_interp2 #a #b #r
  {| EMB.embedding a |} {| EMB.embedding b |}
  {| EMB.embedding r |}
  (f : a -> b -> r)
  : interp_t

val mk_nbe_interp2 #a #b #r
  {| NBE.embedding a |} {| NBE.embedding b |}
  {| NBE.embedding r |}
  (f : a -> b -> r)
  : nbe_interp_t

val mk_interp3 #a #b #c #r
  {| EMB.embedding a |} {| EMB.embedding b |} {| EMB.embedding c |}
  {| EMB.embedding r |}
  (f : a -> b -> c -> r)
  : interp_t

val mk_nbe_interp3 #a #b #c #r
  {| NBE.embedding a |} {| NBE.embedding b |} {| NBE.embedding c |}
  {| NBE.embedding r |}
  (f : a -> b -> c -> r)
  : nbe_interp_t

val mk_interp4 #a #b #c #d #r
  {| EMB.embedding a |} {| EMB.embedding b |} {| EMB.embedding c |} {| EMB.embedding d |}
  {| EMB.embedding r |}
  (f : a -> b -> c -> d -> r)
  : interp_t

val mk_nbe_interp4 #a #b #c #d #r
  {| NBE.embedding a |} {| NBE.embedding b |} {| NBE.embedding c |} {| NBE.embedding d |}
  {| NBE.embedding r |}
  (f : a -> b -> c -> d -> r)
  : nbe_interp_t

val mk_interp5 #a #b #c #d #e #r
  {| EMB.embedding a |} {| EMB.embedding b |} {| EMB.embedding c |} {| EMB.embedding d |} {| EMB.embedding e |}
  {| EMB.embedding r |}
  (f : a -> b -> c -> d -> e -> r)
  : interp_t

val mk_nbe_interp5 #a #b #c #d #e #r
  {| NBE.embedding a |} {| NBE.embedding b |} {| NBE.embedding c |} {| NBE.embedding d |} {| NBE.embedding e |}
  {| NBE.embedding r |}
  (f : a -> b -> c -> d -> e -> r)
  : nbe_interp_t

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

(* Duplication for op_Division / op_Modulus which can prevent reduction. The `f`
already returns something in the option monad, so we add an extra join. Also for
decidable eq which needs different impls in each normalizer *)
val mk1' #a #r #na #nr
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding na |}
  {| EMB.embedding r |} {| NBE.embedding nr |}
  (f : a -> option r)
  (f : na -> option nr)
  : primitive_step

val mk1_psc' #a #r #na #nr
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding na |}
  {| EMB.embedding r |} {| NBE.embedding nr |}
  (f : psc -> a -> option r)
  (f : psc -> na -> option nr)
  : primitive_step

val mk2' #a #b #r #na #nb #nr
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding na |}
  {| EMB.embedding b |} {| NBE.embedding nb |}
  {| EMB.embedding r |} {| NBE.embedding nr |}
  (f : a -> b -> option r)
  (f : na -> nb -> option nr)
  : primitive_step

val mk3' #a #b #c #r #na #nb #nc #nr
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding na |}
  {| EMB.embedding b |} {| NBE.embedding nb |}
  {| EMB.embedding c |} {| NBE.embedding nc |}
  {| EMB.embedding r |} {| NBE.embedding nr |}
  (f : a -> b -> c -> option r)
  (f : na -> nb -> nc -> option nr)
  : primitive_step

val mk4' #a #b #c #d #r #na #nb #nc #nd #nr
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding na |}
  {| EMB.embedding b |} {| NBE.embedding nb |}
  {| EMB.embedding c |} {| NBE.embedding nc |}
  {| EMB.embedding d |} {| NBE.embedding nd |}
  {| EMB.embedding r |} {| NBE.embedding nr |}
  (f : a -> b -> c -> d -> option r)
  (f : na -> nb -> nc -> nd -> option nr)
  : primitive_step


val mk5' #a #b #c #d #e #r #na #nb #nc #nd #ne #nr
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding na |}
  {| EMB.embedding b |} {| NBE.embedding nb |}
  {| EMB.embedding c |} {| NBE.embedding nc |}
  {| EMB.embedding d |} {| NBE.embedding nd |}
  {| EMB.embedding e |} {| NBE.embedding ne |}
  {| EMB.embedding r |} {| NBE.embedding nr |}
  (f : a -> b -> c -> d -> e -> option r)
  (f : na -> nb -> nc -> nd -> ne -> option nr)
  : primitive_step

val mk6' #a #b #c #d #e #f #r #na #nb #nc #nd #ne #nf #nr
  (u_arity : int)
  (name : Ident.lid)
  {| EMB.embedding a |} {| NBE.embedding na |}
  {| EMB.embedding b |} {| NBE.embedding nb |}
  {| EMB.embedding c |} {| NBE.embedding nc |}
  {| EMB.embedding d |} {| NBE.embedding nd |}
  {| EMB.embedding e |} {| NBE.embedding ne |}
  {| EMB.embedding f |} {| NBE.embedding nf |}
  {| EMB.embedding r |} {| NBE.embedding nr |}
  (f : a -> b -> c -> d -> e -> f -> option r)
  (f : na -> nb -> nc -> nd -> ne -> nf -> option nr)
  : primitive_step
