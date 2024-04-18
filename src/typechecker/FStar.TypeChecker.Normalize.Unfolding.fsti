module FStar.TypeChecker.Normalize.Unfolding

open FStar.Compiler.Effect
open FStar.TypeChecker
open FStar.Syntax.Syntax
open FStar.TypeChecker.Cfg

(* This reference stores the max amount of warnings we emit
about unfolding plugins. Set by normalize (0 otherwise). *)
val plugin_unfold_warn_ctr : ref int

(* Exposed for NBE *)
type should_unfold_res =
    | Should_unfold_no
    | Should_unfold_yes
    | Should_unfold_fully
    | Should_unfold_reify

val should_unfold : cfg
                 -> should_reify:(cfg -> bool)
                 -> fv
                 -> Env.qninfo
                 -> should_unfold_res
