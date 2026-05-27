(*
   Copyright 2025 Microsoft Research

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

module Pulse.Checker.Prover.RewritesTo
open Pulse.Syntax
open Pulse.Typing.Env
module PS = Pulse.Checker.Prover.Substs
module R = FStar.Reflection.V2

let is_rewrites_to_p (t: typ) : option (term & term) =
  let hd, args = R.collect_app_ln t in
  match R.inspect_ln hd, args with
  | R.Tv_UInst hd _, [_; lhs, _; rhs, _] ->
    if R.inspect_fv hd <> Pulse.Typing.rewrites_to_p_lid then None else
    Some (lhs, rhs)
  | _ -> None

let extract_rewrites_to_p (t: typ) =
  match is_squash t with
  | None -> None
  | Some t ->
    match is_rewrites_to_p t with
    | None -> None
    | Some (lhs, rhs) ->
      match R.inspect_ln lhs with
      | R.Tv_Var x ->
        let x = R.inspect_namedv x in
        Some (x.uniq, rhs)
      | _ -> None

let maybe_add_binding_to_subst (ss: PS.ss_t) (t: typ) =
  match extract_rewrites_to_p t with
  | Some (x, t) -> if PS.contains ss x then ss else PS.push ss x t
  | None -> ss

let get_subst_from_env g =
  let rec go (ss: PS.ss_t) (bs: env_bindings) : Tot PS.ss_t (decreases bs) =
    match bs with
    | BindingVar { ty } :: bs -> go (maybe_add_binding_to_subst ss ty) bs
    | _ :: bs -> go ss bs
    | [] -> ss in
  go PS.empty (bindings g)

let get_new_substs_from_env g g' ss =
  let rec go (ss: PS.ss_t) (bs: env_bindings) : Tot PS.ss_t (decreases bs) =
    match bs with
    | BindingVar { x; ty } :: bs ->
      let ss = if contains_var g x then ss else 
        maybe_add_binding_to_subst ss ty in
      go ss bs
    | _ :: bs -> go ss bs
    | [] -> ss in
  go ss (bindings g')