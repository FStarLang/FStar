(*
   Copyright 2016 Microsoft Research

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

(** Convert Parser.Ast to Pprint.document for prettyprinting. *)
module FStarC.Parser.ToDocument
open FStarC.Effect

val term_to_document : FStarC.Parser.AST.term -> FStarC.Pprint.document
val decl_to_document   : FStarC.Parser.AST.decl -> FStarC.Pprint.document
val signature_to_document : FStarC.Parser.AST.decl -> FStarC.Pprint.document
val pat_to_document : FStarC.Parser.AST.pattern -> FStarC.Pprint.document
val binder_to_document : FStarC.Parser.AST.binder -> FStarC.Pprint.document
val modul_to_document  : FStarC.Parser.AST.modul -> FStarC.Pprint.document
val comments_to_document : list (string & FStarC.Range.range) -> FStarC.Pprint.document
val modul_with_comments_to_document : FStarC.Parser.AST.modul -> list (string & FStarC.Range.range) -> FStarC.Pprint.document & list (string & FStarC.Range.range)
val handleable_args_length : FStarC.Ident.ident -> int
val decl_with_comments_to_document : FStarC.Parser.AST.decl -> list (string & FStarC.Range.range) -> FStarC.Pprint.document & list (string & FStarC.Range.range)