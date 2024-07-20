(*
   Copyright 2023 Microsoft Research

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

module PulseSyntaxExtension.Env
open FStar.Compiler.Effect
// module Sugar = PulseSugar
module SW = PulseSyntaxExtension.SyntaxWrapper
module A = FStar.Parser.AST
module D = FStar.Syntax.DsEnv
module S = FStar.Syntax.Syntax
module L = FStar.Compiler.List
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst
module R = FStar.Compiler.Range
module BU = FStar.Compiler.Util
module P =  FStar.Syntax.Print
module ToSyntax = FStar.ToSyntax.ToSyntax
open FStar.Class.Show
open FStar.Class.HasRange
open FStar.Class.Monad
open FStar.Ident
open FStar.List.Tot
open PulseSyntaxExtension.Err

let r_ = FStar.Compiler.Range.dummyRange
#push-options "--warn_error -272" //intentional top-level effects
let admit_lid = Ident.lid_of_path ["Prims"; "admit"] r_
let pulse_lib_core_lid l = Ident.lid_of_path (["Pulse"; "Lib"; "Core"]@[l]) r_
let pulse_lib_ref_lid l = Ident.lid_of_path (["Pulse"; "Lib"; "Reference"]@[l]) r_
let prims_exists_lid = Ident.lid_of_path ["Prims"; "l_Exists"] r_
let prims_forall_lid = Ident.lid_of_path ["Prims"; "l_Forall"] r_
let unreachable_lid = pulse_lib_core_lid "unreachable"
let forall_lid = pulse_lib_core_lid "op_forall_Star"
let exists_lid = pulse_lib_core_lid "op_exists_Star"
let star_lid = pulse_lib_core_lid "op_Star_Star"
let emp_lid = pulse_lib_core_lid "emp"
let pure_lid = pulse_lib_core_lid "pure"
let stt_lid = pulse_lib_core_lid "stt"
let assign_lid = pulse_lib_ref_lid "op_Colon_Equals"
let stt_ghost_lid = pulse_lib_core_lid "stt_ghost"
let stt_unobservable_lid = pulse_lib_core_lid "stt_unobservable"
let stt_atomic_lid = pulse_lib_core_lid "stt_atomic"
let op_colon_equals_lid r = Ident.lid_of_path ["op_Colon_Equals"] r
let op_array_assignment_lid r = Ident.lid_of_path ["op_Array_Assignment"] r
let op_bang_lid = pulse_lib_ref_lid "op_Bang"
#pop-options

let read (x:ident) = 
  let open A in
  let range = Ident.range_of_id x in
  let level = Un in
  let head : A.term = {tm = Var op_bang_lid; range; level} in
  let arg = {tm = Var (Ident.lid_of_ids [x]); range; level} in
  {tm = App (head, arg, Nothing); range; level}


(* Environments and name handling utilities *)
type env_t = { 
  dsenv: D.env;
  local_refs: list ident
}

let name = list string

let push_bv env x =
  let dsenv, bv = D.push_bv env.dsenv x in
  { env with dsenv }, bv

let rec push_bvs env xs =
  match xs with
  | [] -> env, []
  | x::xs ->
    let env, bv = push_bv env x in
    let env, bvs = push_bvs env xs in
    env, bv::bvs

let push_namespace env lid =
  let dsenv = D.push_namespace env.dsenv lid in
  {env with dsenv}


let resolve_lid (env:env_t) (lid:lident)
  : err lident
  = match D.try_lookup_lid env.dsenv lid with
    | None -> 
      fail (BU.format1 "Name %s not found" (show lid)) (pos lid)
    | Some t ->
      match (SS.compress t).n with
      | S.Tm_fvar fv -> return (S.lid_of_fv fv)
      | _ -> 
        fail (BU.format2 "Name %s resolved unexpectedly to %s" (show lid) (show t))
             (pos lid)

let resolve_names (env:env_t) (ns:option (list lident)) 
  : err (option (list lident))
  = match ns with
    | None -> return None
    | Some ns -> let! ns = mapM (resolve_lid env) ns in return (Some ns)

// the list A.term is the binder attributes
let destruct_binder (b:A.binder)
: A.aqual & ident & A.term & list A.term
= let attrs = b.battributes in
  match b.b with
  | A.Annotated (x, t)
  | A.TAnnotated (x, t) ->
    b.aqual, x, t, attrs
  | A.NoName t ->
    b.aqual, Ident.id_of_text "_", t, attrs
  | A.Variable x
  | A.TVariable x ->
    b.aqual, x, A.mk_term A.Wild (Ident.range_of_id x) A.Un, attrs

let free_vars_list (#a:Type0) (f : env_t -> a -> list ident) (env:env_t) (xs : list a) : list ident =
  L.collect (f env) xs

let rec free_vars_term (env:env_t) (t:A.term) =
  ToSyntax.free_vars false env.dsenv t

and free_vars_binders (env:env_t) (bs:Sugar.binders)
  : env_t & list ident
  = match bs with
    | [] -> env, []
    | b::bs ->
      let _, x, t, attrs = destruct_binder b in
      let fvs = free_vars_term env t in
      let fvs_attrs = free_vars_list free_vars_term env attrs in
      let env', res = free_vars_binders (fst (push_bv env x)) bs in
      env', fvs@fvs_attrs@res

let free_vars_slprop (env:env_t) (t:Sugar.slprop) =
  let open PulseSyntaxExtension.Sugar in
  match t.v with
  | SLPropTerm t -> free_vars_term env t

let free_vars_comp (env:env_t) (c:Sugar.computation_type)
  : list ident
  = let ids =
        free_vars_slprop env c.precondition @
        free_vars_term env c.return_type @
        free_vars_slprop (fst (push_bv env c.return_name)) c.postcondition
    in
    L.deduplicate Ident.ident_equals ids

let pat_vars (p:A.pattern)
  : err (list ident)
  = let r = p.prange in
    match p.pat with
    | A.PatVar (id, _, _) ->
      return [id]
    | A.PatWild _
    | A.PatConst _
    | A.PatName _ ->
      return []
    | A.PatApp (_, args) ->
      let! vars = 
        args |>
        mapM (fun (p:A.pattern) ->
                match p.pat with
                | A.PatVar (id, _, _) -> return [id]
                | A.PatWild _ -> return []
                | _ -> fail "invalid pattern: no deep patterns allowed" r)
      in
      return (List.Tot.flatten vars)

    | _ ->
      fail "invalid pattern" r
