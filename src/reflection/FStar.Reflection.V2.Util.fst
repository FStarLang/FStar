(*
   Copyright 2008-2022 Microsoft Research

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
module FStar.Reflection.V2.Util

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Order
open FStar.TypeChecker.Env
open FStar.Reflection.V2.Data

open FStar.Class.Show

#set-options "--print_full_names"

module RB = FStar.Reflection.V2.Builtins
module RD = FStar.Reflection.V2.Data
module RE = FStar.Reflection.V2.Embeddings
module RC = FStar.Reflection.V2.Constants
module BU = FStar.Compiler.Util
module U = FStar.Syntax.Util

let unfold_quotation (qt:term) (qi:quoteinfo) : term =
  match qi with
  | { qkind = Quote_static; antiquotations = (shift, aqs) } ->
    match RB.inspect_ln qt with
    (* If it's a variable, check whether it's an antiquotation or just a bvar node *)
    | RD.Tv_BVar bv when bv.index < shift ->
      (* just a local bvar *)
      let tv' = RD.Tv_BVar bv in
      let tv = embed tv' qt.pos None id_norm_cb in
      let t = U.mk_app (RC.refl_constant_term RC.fstar_refl_pack_ln) [as_arg tv] in
      t
    
    | RD.Tv_BVar bv ->
      (* actual antiquotation *)
      let tm = lookup_aq bv (shift, aqs) in
      tm
    
    | tv ->
      (* Else, just unfold by expanding the view, and generating
      a pack call. *)
      let tv = embed #_ #(RE.e_term_view_aq (shift, aqs)) tv qt.pos None id_norm_cb in
      let t = U.mk_app (RC.refl_constant_term RC.fstar_refl_pack_ln) [as_arg tv] in
      t
