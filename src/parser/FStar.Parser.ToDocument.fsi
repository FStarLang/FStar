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

(** Provide this brackets to _to_document. pp_br is the usual way to bracket
    (nothing for decls, {(**,*)} for fdoc. *)
type brackets = 
    { decl_openb : FStar.Pprint.document; decl_closeb : FStar.Pprint.document;
      fdoc_openb : FStar.Pprint.document; fdoc_closeb : FStar.Pprint.document }
val pp_br : brackets 

val doc_of_fsdoc : brackets -> FStar.Parser.AST.fsdoc -> FStar.Pprint.document
val term_to_document : FStar.Parser.AST.term -> FStar.Pprint.document
// [decl_to_document print_fsdoc d]
val decl_to_document   : brackets -> FStar.Parser.AST.decl -> FStar.Pprint.document
val modul_to_document  : brackets -> FStar.Parser.AST.modul -> FStar.Pprint.document
val comments_to_document : list<(string * FStar.Range.range)> -> FStar.Pprint.document
val modul_with_comments_to_document : brackets -> FStar.Parser.AST.modul -> list<(string * FStar.Range.range)> -> FStar.Pprint.document * list<(string * FStar.Range.range)>
val handleable_args_length : FStar.Ident.ident -> int
