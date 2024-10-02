module FStar.Issue
open FStar.Range

module Pprint = FStar.Stubs.Pprint

new
val issue : Type0

let issue_level_string = s:string {
  s == "Info" \/
  s == "Warning" \/
  s == "Error" \/
  s == "Feature not yet implemented: "
}

val message_of_issue (i:issue) : Tot (list Pprint.document)

val level_of_issue (i:issue) : Tot issue_level_string

val number_of_issue (i:issue) : Tot (option int)

val range_of_issue (i:issue) : Tot (option range)

val context_of_issue (i:issue) : Tot (list string)

val render_issue (i:issue) : Tot string
  
(* NOTE: the only way to build a document that actually reduces
in interpreted mode (like in tactics when not using plugins)
is using arbitrary_string, as below. *)
val mk_issue_doc (i:issue_level_string)
             (msg:list Pprint.document)
             (range:option range)
             (number:option int)
             (ctx:list string)
  : Tot issue

(* These qualifiers here to make sure that karamel (while building
krmllib) does not attempt to extract this definition, as that would fail
since it does not have an implementation of arbitrary_string. We could
also not extract this module altogether. *)
noextract
inline_for_extraction
let mk_issue (i:issue_level_string)
             (msg:string)
             (range:option range)
             (number:option int)
             (ctx:list string)
  = mk_issue_doc i [Pprint.arbitrary_string msg] range number ctx
