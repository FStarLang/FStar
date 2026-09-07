(*
   Copyright 2026 Microsoft Research

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

module Pulse.Eta

open FStar.Reflection.V2
open Pulse.Syntax.Base
open Pulse.Reflection.Util
open Pulse.Typing.Env
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RU = Pulse.RuntimeUtils

(* Depth of nesting we are willing to expand through. Expansion recurses into
   component types, which are strictly smaller than the tuple type, so this is
   only a guard against a pathological type. *)
let max_depth = 16

let uv_unk : universe = R.pack_universe R.Uv_Unk

let dbg (g:env) (f: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "eta" then T.print (f ()) else ()

(* Is [ty] (the whnf of) a [tuple2] application? If so, its two universes and
   two component types. *)
let is_tuple2_ty (g:env) (ty:typ) : T.Tac (option (universe & universe & typ & typ)) =
  let ty = RU.whnf_lax (elab_env g) ty in
  dbg g (fun _ -> "eta: is_tuple2_ty on " ^ T.term_to_string ty);
  match T.hua ty with
  | Some (h, us, args) ->
    if implode_qn (T.inspect_fv h) = `%tuple2
    then
      match args with
      | [(a1, Q_Explicit); (a2, Q_Explicit)] ->
        let u1, u2 =
          match us with
          | [u1; u2] -> u1, u2
          | _ -> uv_unk, uv_unk
        in
        Some (u1, u2, a1, a2)
      | _ -> None
    else None
  | _ -> None

(* If [t] is a tuple projection, the term being projected. *)
let is_projected (t:term) : T.Tac (option term) =
  match T.hua t with
  | Some (h, _, args) ->
    let n = implode_qn (T.inspect_fv h) in
    if n = `%Mktuple2?._1 || n = `%fst
    || n = `%Mktuple2?._2 || n = `%snd
    then
      match args with
      | [(_, Q_Implicit); (_, Q_Implicit); (x, Q_Explicit)] -> Some x
      | _ -> None
    else None
  | _ -> None

(* Returns the fresh holes introduced, i.e. the leaves of the expansion; empty
   if nothing was expanded. Callers hand these to F*'s uni-valued rule, which
   can then solve any of them sitting at [unit]. *)
let rec eta_expand_uvar' (g:env) (t:term) (fuel:nat) : T.Tac (list term) =
  if fuel = 0 then []
  else
    match RU.uvar_typ t with
    | None -> dbg g (fun _ -> "eta: not a uvar: " ^ T.term_to_string t); []
    | Some ty ->
      match is_tuple2_ty g ty with
      | None -> []
      | Some (u1, u2, a1, a2) ->
        let r = RU.range_of_term t in
        let reason = "eta-expansion of a product-typed hole" in
        let v1 = RU.new_implicit_var reason r (elab_env g) a1 false in
        let v2 = RU.new_implicit_var reason r (elab_env g) a2 false in
        if RU.teq_nosmt_force (elab_env g) t (mk_mktuple2 u1 u2 a1 a2 v1 v2)
        then
          (* A component may itself be a product. *)
          let leaves (v:term) : T.Tac (list term) =
            match eta_expand_uvar' g v (fuel - 1) with
            | [] -> [v]
            | l -> l
          in
          leaves v1 @ leaves v2
        else []

let eta_expand_uvar (g:env) (t:term) : T.Tac (list term) =
  eta_expand_uvar' g t max_depth

let rec eta_projected' (g:env) (t:term) (fuel:nat) : T.Tac (list term) =
  if fuel = 0 then []
  else
    let here =
      match is_projected t with
      | Some x ->
        dbg g (fun _ -> "eta: projected " ^ T.term_to_string x);
        eta_expand_uvar g x
      | None -> []
    in
    let _, args = T.collect_app_ln t in
    here @ eta_projected_args g args (fuel - 1)

and eta_projected_args (g:env) (args:list argv) (fuel:nat) : T.Tac (list term) =
  match args with
  | [] -> []
  | (a, _) :: args ->
    let l1 = eta_projected' g a fuel in
    l1 @ eta_projected_args g args fuel

let eta_expand_projected_uvars (g:env) (t:term) : T.Tac (list term) =
  eta_projected' g t max_depth

let rec eta_term' (g:env) (t:term) (fuel:nat) : T.Tac (list term) =
  if fuel = 0 then []
  else
    let l = eta_expand_uvar g t in
    if Cons? l then l
    else
      let _, args = T.collect_app_ln t in
      eta_term_args g args (fuel - 1)

and eta_term_args (g:env) (args:list argv) (fuel:nat) : T.Tac (list term) =
  match args with
  | [] -> []
  | (a, _) :: args ->
    let l1 = eta_term' g a fuel in
    l1 @ eta_term_args g args fuel

let eta_expand_term_uvars (g:env) (t:term) : T.Tac (list term) =
  eta_term' g t max_depth
