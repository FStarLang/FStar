(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Errors.Msg

(* Allows constructing structured pretty-printed error messages. *)

open FStar.Pprint

(* An error message is a list of documents. This allows us to print errors like
these:

* Error 19 at tests/error-messages/Bug1997.fst(92,19-92,49):
  - Assertion failed
  - The SMT solver could not prove the query. Use --query_stats for more details.
  - Also see: Prims.fst(96,32-96,42)

The header is taken from the code and range, and then the documents are rendered
in order.

`empty` documents in the list are skipped.
*)
type error_message = list document

(* A helper for creating errors from strings, only to be used for text.
This will split the string into words and format is a paragraph.

If you call this with a string containing a pretty-printed term (or
anything else) all its formatting will be lost. You should instead use
[term_to_doc] or similar to work with the documents directly, or as a
last resort use doc_of_string. *)
val text : string -> document

(* Create a simple error message from a string. If the string is just
text and can be long, please use [text] instead. On the other hand, if
you need to respect indentation/spacing in the string, then use this
one, but if that's the case it's probably better to build a doc instead
of lifting from a string. NB: mkmsg s is equal to [doc_of_string s]. *)
val mkmsg : string -> error_message
