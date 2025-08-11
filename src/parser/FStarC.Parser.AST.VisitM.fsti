module FStarC.Parser.AST.VisitM

open FStarC
open FStarC.Effect
open FStarC.Parser.AST
open FStarC.Class.Monad
module AST = FStarC.Parser.AST

(* This module exposes a very generic visitor for surface terms.  This is very
similar to Syntax.VisitM for internal terms, but with less convenience
functions. The user is expected to construct and use the relevant records.
Deriving a visitor like this should not be too difficult.

The one non-uniformity is the `with_binder` field that allows users to write
scoping-aware visitors. Not sure how this could be determined in a general way
if this visitor was derived. *)

type endo (m : Type -> Type) a = a -> m a

(* I'm writing this in a very uniform style. Every type in the
recursive group gets a configurable visitor function. *)
noeq
type dict (m : Type -> Type) = {
  f_term'                    : endo m term';
  f_term                     : endo m term;
  f_match_returns_annotation : endo m match_returns_annotation;
  f_patterns                 : endo m patterns; (* smt patterns, not branches *)
  f_calc_step                : endo m calc_step;
  f_attributes_              : endo m attributes_;
  f_binder'                  : endo m binder';
  f_binder                   : endo m binder;
  f_pattern'                 : endo m pattern';
  f_pattern                  : endo m pattern;
  f_branch                   : endo m branch;
  f_arg_qualifier            : endo m arg_qualifier;
  f_aqual                    : endo m aqual;
  f_imp                      : endo m imp;
}

val nops #m {| monad m |} : dict m

val tie #m {| monad m |} (pre post : dict m) : dict m

(* bottom up *)
val tie_bu #m {| monad m |} (d : dict m) : dict m

(* top down *)
val tie_td #m {| monad m |} (d : dict m) : dict m
