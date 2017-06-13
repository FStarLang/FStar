module FStar.Tactics

(* I don't expect many uses of tactics without syntax handling *)
include FStar.Reflection.Syntax
include FStar.Reflection.Formula

include FStar.Tactics.Effect
include FStar.Tactics.Builtins
include FStar.Tactics.Derived
include FStar.Tactics.Logic
