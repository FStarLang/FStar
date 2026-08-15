(*
   Copyright 2008-2025 Microsoft Research

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

module FStarC.TypeChecker.Overload

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Pprint
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.Class.Show
open FStarC.Class.PP

module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module Env = FStarC.TypeChecker.Env
module Print = FStarC.Syntax.Print

let dbg = Debug.get_toggle "Overload"

instance showable_base_typ : showable base_typ = {
  show = (function
          | Base_rigid fv -> "Base_rigid " ^ show fv
          | Base_type -> "Base_type"
          | Base_unknown -> "Base_unknown");
}

(* The normalization steps that define what "the base type" means: strip
   ascriptions, strip metadata, and strip refinements, so that x:nat{x > 17}
   and int agree. This is the same normalization the projector resolution path
   has always used. *)
let base_steps : list Env.step = [Unascribe; Unmeta; Unrefine]

let base_of_typ env t =
  let t = N.unfold_whnf' base_steps env t in
  let hd, _ = U.head_and_args_full t in
  let r =
    match (SS.compress (U.un_uinst hd)).n with
    | Tm_fvar fv -> Base_rigid fv
    | Tm_type _ -> Base_type
    | _ -> Base_unknown
  in
  if !dbg then
    Format.print2 "(Overload) base_of_typ %s = %s\n" (show t) (show r);
  r

let base_head_fv env t =
  match base_of_typ env t with
  | Base_rigid fv -> Some fv
  | _ -> None

let compatible b1 b2 =
  match b1, b2 with
  | Base_unknown, _
  | _, Base_unknown -> true
  | Base_type, Base_type -> true
  | Base_rigid fv1, Base_rigid fv2 -> fv_eq fv1 fv2
  | _ -> false

let formals_of_typ env t =
  (* unfold_whnf sees through type abbreviations, so a candidate declared as
     [val f : my_abbrev] still exposes its binders. *)
  U.arrow_formals_comp (N.unfold_whnf env t)

let nth_explicit_formal_base env t i =
  let bs, _ = formals_of_typ env t in
  let explicit = bs |> List.filter (fun b -> not (is_bqual_implicit_or_meta b.binder_qual)) in
  if i < 0 || i >= List.length explicit
  then Base_unknown
  else base_of_typ env (List.nth explicit i).binder_bv.sort

let arity_compatible env t n =
  let bs, c = formals_of_typ env t in
  let n_explicit = bs |> List.filter (fun b -> not (is_bqual_implicit_or_meta b.binder_qual)) |> List.length in
  if n <= n_explicit
  then true
  else
    (* Not enough binders at the top, but the result may still be a function:
       a type abbreviation we have not unfolded, or something whose type is not
       yet known. [base_of_typ] normalizes, so a rigid head at this point really
       cannot be applied any further; anything else might. *)
    match base_of_typ env (U.comp_result c) with
    | Base_rigid _
    | Base_type -> false
    | Base_unknown -> true

let candidates_doc env cands =
  cands |> List.map (fun fv ->
    let l = lid_of_fv fv in
    let ty =
      match Env.try_lookup_lid env l with
      | Some ((_, t), _) -> pp t
      | None -> doc_of_string "<unknown type>"
    in
    group (pp l ^^ doc_of_string " :" ^/^ align ty))
