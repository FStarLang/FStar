(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStar.Syntax.Print.Pretty

open FStar.Compiler
open FStar.Syntax.Syntax
open FStar.Compiler.Util
module Resugar    = FStar.Syntax.Resugar
module ToDocument = FStar.Parser.ToDocument
module Pp         = FStar.Pprint

let rfrac = float_of_string "1.0"
let width = 100
let pp d = Pp.pretty_string rfrac 100 d

let term_to_string' env (tm:term) : string = Ident.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_term' env tm in
  let d = ToDocument.term_to_document e in
  pp d
)

let comp_to_string' env (c:comp) : string = Ident.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_comp' env c in
  let d = ToDocument.term_to_document e in
  pp d
)

let sigelt_to_string' env (se:sigelt) : string = Ident.with_frozen_gensym (fun () ->
  match Resugar.resugar_sigelt' env se with
  | None -> ""
  | Some d ->
    let d = ToDocument.decl_to_document d in
    pp d
)

(* These three are duplicated instead of being a special case
of the above so we can reuse the empty_env created at module
load time for DsEnv. Otherwise we need to create another empty
DsEnv.env here. *)
let term_to_string (tm:term) : string = Ident.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_term tm in
  let d = ToDocument.term_to_document e in
  pp d
)

let comp_to_string (c:comp) : string = Ident.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_comp c in
  let d = ToDocument.term_to_document e in
  pp d
)

let sigelt_to_string (se:sigelt) : string = Ident.with_frozen_gensym (fun () ->
  match Resugar.resugar_sigelt se with
  | None -> ""
  | Some d ->
    let d = ToDocument.decl_to_document d in
    pp d
)

let univ_to_string (u:universe) : string = Ident.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_universe u Range.dummyRange in
  let d = ToDocument.term_to_document e in
  pp d
)

let tscheme_to_string (ts:tscheme) : string = Ident.with_frozen_gensym (fun () ->
  let d = Resugar.resugar_tscheme ts in
  let d = ToDocument.decl_to_document d in
  pp d
)

let pat_to_string (p:pat) : string = Ident.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_pat p Syntax.no_names in
  let d = ToDocument.pat_to_document e in
  pp d
)

let binder_to_string' is_arrow (b:binder) : string = Ident.with_frozen_gensym (fun () ->
  match Resugar.resugar_binder b Range.dummyRange with
  | None -> ""
  | Some e ->
    let d = ToDocument.binder_to_document e in
    pp d
)

let eff_decl_to_string' for_free r q ed = Ident.with_frozen_gensym (fun () ->
  let d = Resugar.resugar_eff_decl r q ed in
  let d = ToDocument.decl_to_document d in
  pp d
)
