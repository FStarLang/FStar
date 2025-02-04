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

module FStarC.Syntax.Print.Pretty
open FStarC

open FStarC
open FStarC.Syntax.Syntax
open FStarC.Util
module Resugar    = FStarC.Syntax.Resugar
module ToDocument = FStarC.Parser.ToDocument
module Pp         = FStarC.Pprint

let rfrac = float_of_string "1.0"
let width = 100
let pp d = Pp.pretty_string rfrac width d

let term_to_doc' env (tm:term) : Pprint.document = GenSym.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_term' env tm in
  ToDocument.term_to_document e
)

let univ_to_doc' env (u:universe) : Pprint.document = GenSym.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_universe' env u Range.dummyRange in
  ToDocument.term_to_document e
)

let term_to_string' env (tm:term) : string = GenSym.with_frozen_gensym (fun () ->
  let d = term_to_doc' env tm in
  pp d
)

let univ_to_string' env (u:universe) : string = GenSym.with_frozen_gensym (fun () ->
  let d = univ_to_doc' env u in
  pp d
)

let comp_to_doc' env (c:comp) : Pprint.document = GenSym.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_comp' env c in
  ToDocument.term_to_document e
)

let comp_to_string' env (c:comp) : string = GenSym.with_frozen_gensym (fun () ->
  let d = comp_to_doc' env c in
  pp d
)

let sigelt_to_doc' env (se:sigelt) : Pprint.document = GenSym.with_frozen_gensym (fun () ->
  match Resugar.resugar_sigelt' env se with
  | None -> Pprint.empty
  | Some d -> ToDocument.decl_to_document d
)

let sigelt_to_string' env (se:sigelt) : string = GenSym.with_frozen_gensym (fun () ->
  let d = sigelt_to_doc' env se in
  pp d
)

(* These are duplicated instead of being a special case
of the above so we can reuse the empty_env created at module
load time for DsEnv. Otherwise we need to create another empty
DsEnv.env here. *)
let term_to_doc (tm:term) : Pprint.document = GenSym.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_term tm in
  ToDocument.term_to_document e
)

let univ_to_doc (u:universe) : Pprint.document = GenSym.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_universe u Range.dummyRange in
  ToDocument.term_to_document e
)

let comp_to_doc (c:comp) : Pprint.document = GenSym.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_comp c in
  ToDocument.term_to_document e
)

let sigelt_to_doc (se:sigelt) : Pprint.document = GenSym.with_frozen_gensym (fun () ->
  match Resugar.resugar_sigelt se with
  | None -> Pprint.empty
  | Some d -> ToDocument.decl_to_document d
)

let term_to_string (tm:term) : string = GenSym.with_frozen_gensym (fun () ->
  let d = term_to_doc tm in
  pp d
)

let comp_to_string (c:comp) : string = GenSym.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_comp c in
  let d = ToDocument.term_to_document e in
  pp d
)

let sigelt_to_string (se:sigelt) : string = GenSym.with_frozen_gensym (fun () ->
  match Resugar.resugar_sigelt se with
  | None -> ""
  | Some d ->
    let d = ToDocument.decl_to_document d in
    pp d
)

let univ_to_string (u:universe) : string = GenSym.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_universe u Range.dummyRange in
  let d = ToDocument.term_to_document e in
  pp d
)

let tscheme_to_doc (ts:tscheme) : Pprint.document = GenSym.with_frozen_gensym (fun () ->
  let d = Resugar.resugar_tscheme ts in
  ToDocument.decl_to_document d
)

let tscheme_to_string (ts:tscheme) : string =
  tscheme_to_doc ts |> pp

let pat_to_string (p:pat) : string = GenSym.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_pat p (Class.Setlike.empty ()) in
  let d = ToDocument.pat_to_document e in
  pp d
)

let binder_to_string' is_arrow (b:binder) : string = GenSym.with_frozen_gensym (fun () ->
  let e = Resugar.resugar_binder b Range.dummyRange in
  let d = ToDocument.binder_to_document e in
  pp d
)

let eff_decl_to_string ed = GenSym.with_frozen_gensym (fun () ->
  let d = Resugar.resugar_eff_decl ed in
  let d = ToDocument.decl_to_document d in
  pp d
)
