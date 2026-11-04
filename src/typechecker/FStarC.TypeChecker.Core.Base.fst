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
module FStarC.TypeChecker.Core.Base

(* See the interface. *)

open FStarC.TypeChecker.CommonBase
open FStarC
open FStar.List.Tot
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.Errors.Msg { fquotes }
module Env = FStarC.TypeChecker.Env
module S = FStarC.Syntax.Syntax
module R = FStarC.Range
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module PC = FStarC.Parser.Const
module I = FStarC.Ident
module BU = FStarC.Util
module VCUtil = FStarC.TypeChecker.VCUtil
module UnivEq = FStarC.TypeChecker.UnivEq
module UniverseOf = FStarC.TypeChecker.UniverseOf
module Termination = FStarC.TypeChecker.Termination
module Err = FStarC.TypeChecker.Err
module Hash = FStarC.Syntax.Hash
module Subst = FStarC.Syntax.Subst
module TEQ = FStarC.TypeChecker.TermEqAndSimplify
module Visit = FStarC.Syntax.Visit

open FStarC.Class.Show
open FStarC.Class.Setlike
open FStarC.Class.Tagged
open FStarC.Class.PP
open FStarC.Syntax.Print {}

open FStarC.Pprint
open FStarC.Errors.Msg { text }

let dbg       = Debug.get_toggle "Core"

let dbg_facts = Debug.get_toggle "CoreFacts"

let dbg_Eq    = Debug.get_toggle "CoreEq"

let dbg_Top   = Debug.get_toggle "CoreTop"

let dbg_Exit  = Debug.get_toggle "CoreExit"

let dbg_DisableCoreCache = Debug.get_toggle "DisableCoreCache"

let eff_to_lid (e:eff) : I.lident =
  match e with
  | ETot -> PC.primitive_pure_lid
  | EGhost -> PC.primitive_ghost_lid
  | EEff m -> m

instance showable_eff : showable eff = {
  show = (function
          | ETot -> "Tot"
          | EGhost -> "GTot"
          | EEff m -> show m);
}

let eff_eq (e0 e1:eff) : ML bool =
  match e0, e1 with
  | ETot, ETot
  | EGhost, EGhost -> true
  | EEff m0, EEff m1 -> I.lid_equals m0 m1
  | _ -> false

let debug g (f: unit -> ML unit) : ML unit =
  if !dbg
  then f ()

let relation_to_string = function
  | EQUALITY -> "=?="
  | SUBTYPING None -> "<:?"
  | SUBTYPING (Some (tm, _)) -> Format.fmt1 "( <:? %s)" (show tm)

instance showable_rel : showable relation = {
    show = fun rel ->
      match rel with
      | EQUALITY -> "=?="
      | SUBTYPING _ -> "<:?"
}

let context_term_to_string (c:context_term) =
  match c with
  | CtxTerm term -> show term
  | CtxRel t0 r t1 ->
    Format.fmt3 "%s %s %s"
              (show t0)
              (relation_to_string r)
              (show t1)

(* The instance prints some brief info on the error_context. `print_context`
below is a full printer. *)
instance showable_context : showable context = {
  show = (fun context -> Format.fmt3 "{no_guard=%s; unfolding_ok=%s; error_context=%s}"
                                    (show context.no_guard)
                                    (show context.unfolding_ok)
                                    (show (List.map fst context.error_context)));
}

let print_context (ctx:context)
  : ML string =
  let rec aux (depth:string) (ctx:_) : ML _ =
    match ctx with
    | [] -> ""
    | (msg, ctx_term)::tl ->
      let hd =
        Format.fmt3
          "%s %s (%s)\n"
          depth
          msg
          (match ctx_term with None -> "" | Some ctx_term -> context_term_to_string ctx_term)
      in
      let tl = aux (depth ^ ">") tl in
      hd ^ tl
  in
  aux "" (List.rev ctx.error_context)

let print_error (err:error) =
  let ctx, msg, _ = err in
  Format.fmt2 "%s%s" (print_context ctx) (Errors.Msg.rendermsg msg)

instance showable_error : showable error = { show = print_error }

let print_error_short (err:error) =
  let _, msg, _ = err in
  Errors.Msg.rendermsg msg

let error_code (err:error) : ML (option Errors.error_code) =
  let _, _, c = err in c

let error_message (err:error) : ML Errors.error_message =
  let _, msg, _ = err in msg

(* The position of the innermost term of the error's context that has one. *)
let error_range (err:error) : ML (option R.t) =
  let ctx, _, _ = err in
  let ok (r:R.t) : ML bool = R.file_of_use_range r <> R.file_of_use_range R.dummyRange in
  let ctx_range (c:context_term) : ML (option R.t) =
    match c with
    | CtxRel _ (SUBTYPING (Some (tm, _))) _ -> if ok tm.pos then Some tm.pos else None
    | CtxTerm t -> if ok t.pos then Some t.pos else None
    | CtxRel t0 _ _ -> if ok t0.pos then Some t0.pos else None
  in
  List.tryPick (fun (_, c) -> match c with None -> None | Some c -> ctx_range c) ctx.error_context
