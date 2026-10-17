(* Model implementation of FStar.Issue: verified, but never extracted (the real implementation is native). *)
module FStar.Issue

open FStar.Range
module Pprint = FStar.Pprint

noeq
type issue = {
  issue_level : s:string{s == "Info" \/ s == "Warning" \/ s == "Error" \/
                         s == "Feature not yet implemented: "};
  issue_msg : list Pprint.document;
  issue_range : option range;
  issue_number : option int;
  issue_ctx : list string;
}

let message_of_issue i = i.issue_msg
let level_of_issue i = i.issue_level
let number_of_issue i = i.issue_number
let range_of_issue i = i.issue_range
let context_of_issue i = i.issue_ctx
let issue_to_doc i = Pprint.concat i.issue_msg
let render_issue i = Pprint.render (issue_to_doc i)

let mk_issue_doc issue_level issue_msg issue_range issue_number issue_ctx =
  { issue_level; issue_msg; issue_range; issue_number; issue_ctx }
