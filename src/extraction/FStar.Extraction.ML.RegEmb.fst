(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
module FStar.Extraction.ML.RegEmb

(* This module handles registering plugins and generating
embeddings for their types. *)

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Const
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.UEnv
open FStar.Syntax.Syntax

module Print = FStar.Syntax.Print
module BU    = FStar.Compiler.Util
module SS    = FStar.Syntax.Subst
module U     = FStar.Syntax.Util
module PC    = FStar.Parser.Const
module EMB   = FStar.Syntax.Embeddings
module Util  = FStar.Extraction.ML.Util

let do_handle_plugin (g: uenv) (arity_opt: option int) (se: sigelt) : list mlmodule1 =
  // BU.print2 "Got plugin with attrs = %s; arity_opt=%s"
  //          (List.map Print.term_to_string se.sigattrs |> String.concat " ")
  //          (match arity_opt with None -> "None" | Some x -> "Some " ^ string_of_int x);
  let w = with_ty MLTY_Top in
  match se.sigel with
  | Sig_let {lbs} ->
      let mk_registration lb : list mlmodule1 =
         let fv = BU.right lb.lbname in
         let fv_lid = fv.fv_name.v in
         let fv_t = lb.lbtyp in
         let ml_name_str = MLE_Const (MLC_String (Ident.string_of_lid fv_lid)) in
         match Util.interpret_plugin_as_term_fun g fv fv_t arity_opt ml_name_str with
         | Some (interp, nbe_interp, arity, plugin) ->
             let register, args =
               if plugin
               then (["FStar_Tactics_Native"], "register_plugin"), [interp; nbe_interp]
               else (["FStar_Tactics_Native"], "register_tactic"), [interp]
             in
             let h = with_ty MLTY_Top <| MLE_Name register in
             let arity  = MLE_Const (MLC_Int(string_of_int arity, None)) in
             let app = with_ty MLTY_Top <| MLE_App (h, [w ml_name_str; w arity] @ args) in
             [MLM_Top app]
         | None -> []
      in
      List.collect mk_registration (snd lbs)
  | _ -> []

(* When extracting a plugin, each top-level definition marked with a `@plugin` attribute
   is extracted along with an invocation to FStar.Tactics.Native.register_tactic or register_plugin,
   which installs the compiled term as a primitive step in the normalizer
 *)
let maybe_register_plugin (g:uenv) (se:sigelt) : list mlmodule1 =
    let plugin_with_arity attrs =
        BU.find_map attrs (fun t ->
              let head, args = U.head_and_args t in
              if not (U.is_fvar PC.plugin_attr head)
              then None
              else match args with
                   | [({n=Tm_constant (Const_int(s, _))}, _)] ->
                     Some (Some (BU.int_of_string s))
                   | _ -> Some None)
    in
    if Options.codegen() <> Some Options.Plugin
    then []
    else
      match plugin_with_arity se.sigattrs with
      | None -> []
      | Some arity_opt ->
        do_handle_plugin g arity_opt se
