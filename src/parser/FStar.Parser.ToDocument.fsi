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
#light "off"

(** Convert Parser.Ast to Pprint.document for prettyprinting. *)
module FStar.Parser.ToDocument
open FStar.All

val term_to_document : FStar.Parser.AST.term -> FStar.Pprint.document
val decl_to_document   : FStar.Parser.AST.decl -> FStar.Pprint.document
val pat_to_document : FStar.Parser.AST.pattern -> FStar.Pprint.document
val binder_to_document : FStar.Parser.AST.binder -> FStar.Pprint.document
val modul_to_document  : FStar.Parser.AST.modul -> FStar.Pprint.document
val comments_to_document : list<(string * FStar.Range.range)> -> FStar.Pprint.document
val modul_with_comments_to_document : FStar.Parser.AST.modul -> list<(string * FStar.Range.range)> -> FStar.Pprint.document * list<(string * FStar.Range.range)>
val handleable_args_length : FStar.Ident.ident -> int
