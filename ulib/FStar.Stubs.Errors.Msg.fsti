module FStar.Stubs.Errors.Msg

(* Implemented in src/, allows constructing structured pretty-printed error messages. *)

open FStar.Stubs.Pprint

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

(* Makes an indented sublist using bullet as a header for each list element. *)
val sublist : bullet:document -> elems:list document -> document

(* == sublist (doc_of_string "- ") *)
val bulleted : list document -> document

(* Create a simple error message from a string. If the string is just
text and can be long, please use [text] instead. On the other hand, if
you need to respect indentation/spacing in the string, then use this
one, but if that's the case it's probably better to build a doc instead
of lifting from a string. NB: mkmsg s is equal to [doc_of_string s]. *)
val mkmsg : string -> error_message

(* A nested document that can be concatenated with another one *)
val subdoc : document -> document

(* Only to be used by FStar.Errors *)
val renderdoc : document -> string

(* Returns a document with the current stack trace *)
val backtrace_doc : unit -> document

(* Render an error message as a string. *)
val rendermsg : error_message -> string
