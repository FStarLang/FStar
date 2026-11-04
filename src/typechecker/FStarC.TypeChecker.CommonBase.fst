(*
   Copyright Microsoft Research

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
module FStarC.TypeChecker.CommonBase

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Syntax.Print {}
open FStarC.Class.Show
module S = FStarC.Syntax.Syntax
module C = FStarC.Parser.Const

instance showable_guard_formula : showable guard_formula = {
  show = (function
          | Trivial      -> "Trivial"
          | NonTrivial f -> "NonTrivial " ^ show f)
}

let mk_by_tactic tac f
  : ML term =
    let t_by_tactic = S.mk_Tm_uinst (tabbrev C.by_tactic_lid) [U_zero] in
    S.mk_Tm_app t_by_tactic [S.as_arg tac; S.as_arg f] Range.dummyRange

let rec delta_depth_greater_than l m = match l, m with
    | Delta_equational_at_level i, Delta_equational_at_level j -> i > j
    | Delta_constant_at_level i,   Delta_constant_at_level j   -> i > j
    | Delta_abstract d, _                                      -> delta_depth_greater_than d m
    | _, Delta_abstract d                                      -> delta_depth_greater_than l d
    | Delta_equational_at_level _, _                           -> true
    | _, Delta_equational_at_level _                           -> false

let rec decr_delta_depth = function
    | Delta_constant_at_level 0
    | Delta_equational_at_level 0 -> None
    | Delta_constant_at_level i   -> Some (Delta_constant_at_level (i - 1))
    | Delta_equational_at_level i -> Some (Delta_equational_at_level (i - 1))
    | Delta_abstract d            -> decr_delta_depth d

let check_positivity_qual subtyping p0 p1
  = if p0 = p1 then true
    else if subtyping
    then match p0, p1 with
         | Some _, None -> true
         | Some BinderUnused, Some BinderStrictlyPositive -> true
         | _ -> false
    else false
