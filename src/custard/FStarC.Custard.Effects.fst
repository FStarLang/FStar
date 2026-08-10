(*
   Copyright 2008-2026 Microsoft Research

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

module FStarC.Custard.Effects

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Syntax.Syntax
open FStarC.Custard.Syntax
open FStarC.Errors.Msg

module E      = FStarC.Errors
module Ident  = FStarC.Ident
module PC     = FStarC.Parser.Const
module S      = FStarC.Syntax.Syntax
module SS     = FStarC.Syntax.Subst
module TcEnv  = FStarC.TypeChecker.Env
module TcUtil = FStarC.TypeChecker.Util
module U      = FStarC.Syntax.Util

let of_lid (env:TcEnv.env) (l:Ident.lident) : ML eff =
  let l = TcEnv.norm_eff_name env l in
  if Ident.lid_equals l PC.effect_GHOST_lid
  || Ident.lid_equals l PC.effect_Ghost_lid
  then E_Ghost
  else if Ident.lid_equals l PC.effect_PURE_lid
       || Ident.lid_equals l PC.effect_Pure_lid
       || Ident.lid_equals l PC.effect_Tot_lid
  then E_Pure
  else
    (* Everything else is impure.  We do not distinguish [Extract_reify] from
       [Extract_primitive] here: reification changes the *term* we extract, not
       the drop/duplicate/reorder question, which is all [eff] is used for.
       (Custard does not reify yet; a reifiable effect is extracted through its
       representation type, which is the same thing the ML pipeline does after
       reifying.) *)
    match TcUtil.effect_extraction_mode env l with
    | S.Extract_none reason ->
      E.raise_error0 E.Error_CustardUnextractableEffect [
        text ("Custard cannot extract the effect " ^ Ident.string_of_lid l ^ ".");
        text reason
      ]
    | _ -> E_Impure

(* Section 7.2: Pulse's [stt] and friends are not F* effects, they are type
   constructors carrying [@@extract_as_impure_effect].  The attribute has to be
   looked up on the head of the *normalized* codomain, because [stt] is usually
   behind an abbreviation. *)
let head_is_impure_marker (env:TcEnv.env) (t:typ) : ML bool =
  let hd, _ = U.head_and_args_full t in
  match (U.un_uinst hd).n with
  | Tm_fvar fv -> TcEnv.fv_has_attr env fv PC.extract_as_impure_effect_lid
  | _ -> false

let impure_effect_result (env:TcEnv.env) (t:typ) : ML (option typ) =
  let hd, args = U.head_and_args_full t in
  match (U.un_uinst hd).n with
  | Tm_fvar fv when TcEnv.fv_has_attr env fv PC.extract_as_impure_effect_lid ->
    (* [stt a pre post]: the representation is [a], the indices are erased. *)
    (match args with
     | (a, _) :: _ -> Some a
     | [] -> None)
  | _ -> None

let result_typ (env:TcEnv.env) (c:comp) : ML typ =
  let r = U.comp_result c in
  match impure_effect_result env r with
  | Some a -> a
  | None -> r

let of_comp (env:TcEnv.env) (c:comp) : ML eff =
  let e = of_lid env (U.comp_effect_name c) in
  (* The promotion happens on the arrow, so it is visible at every call site of
     every function of that type -- including one reached through a [Poly]
     binder, which is the whole point. *)
  if head_is_impure_marker env (U.comp_result c) then E_Impure else e

(* -------------------------------------------------------------------- *)
(* Reification (section 7.5)                                            *)
(* -------------------------------------------------------------------- *)

let is_reifiable (env:TcEnv.env) (l:Ident.lident) : ML bool =
  match TcUtil.effect_extraction_mode env l with
  | S.Extract_reify -> true
  | _ -> false

(* The steps are the ML extraction's, deliberately: this reduction has to
   *finish the job*.  [reify e] is only a marker, and what makes it a term of
   the representation type is unfolding the effect's [bind] and [return], which
   is what [norm_reify] is for.  Leaving a [Tm_constant Const_reify] in the
   term would reach the translator as a node it has no meaning for. *)
let reify_steps : list TcEnv.step =
  [TcEnv.Inlining; TcEnv.ForExtraction; TcEnv.Unascribe]

let reify_comp (env:TcEnv.env) (c:comp) : ML typ =
  TcEnv.reify_comp env c S.U_unknown

let maybe_reify (env:TcEnv.env) (t:term) (l:Ident.lident) : ML term =
  if is_reifiable env l
  then TcUtil.norm_reify env reify_steps (U.mk_reify t (Some l))
  else t
