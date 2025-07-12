module FStarC.TypeChecker.Normalize.Unfolding

open FStarC.Effect
open FStarC.TypeChecker
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Cfg

(* Exposed for NBE *)
type should_unfold_res =
    | Should_unfold_no
    | Should_unfold_yes
    | Should_unfold_once
    | Should_unfold_fully
    | Should_unfold_reify

val should_unfold : cfg
                 -> should_reify:(cfg -> bool)
                 -> fv
                 -> Env.qninfo
                 -> should_unfold_res
