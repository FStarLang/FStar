type issue_level = FStar_Errors.issue_level
type issue = FStar_Errors.issue
type issue_level_string = string

open FStar_Errors

let string_of_level (i:issue_level)
= match i with
  | ENotImplemented
  | EError -> "Error"
  | EInfo -> "Info"
  | EWarning -> "Warning"

let message_of_issue (i:issue) = i.issue_msg

let level_of_issue (i:issue) = string_of_level (i.issue_level)

let number_of_issue (i:issue) = i.issue_number

let range_of_issue (i:issue) = i.issue_range

let context_of_issue (i:issue) = i.issue_ctx

let mk_issue_level (i:issue_level_string)
  : issue_level
  = match i with
    | "Error" -> EError
    | "Info" -> EInfo
    | "Warning" -> EWarning

let render_issue (i:issue) : string = FStar_Errors.format_issue i

let mk_issue_doc (i:issue_level_string)
             (msg:FStar_Pprint.document list)
             (range:FStar_Compiler_Range.range option)
             (number:Z.t option)
             (ctx:string list)
  = { issue_level = mk_issue_level i;
      issue_msg = msg;
      issue_range = range;
      issue_number = number;
      issue_ctx = ctx }

(* repeated... could be extracted *)
let mk_issue (i:issue_level_string)
             (msg:string)
             (range:FStar_Compiler_Range.range option)
             (number:Z.t option)
             (ctx:string list)
  = { issue_level = mk_issue_level i;
      issue_msg = [FStar_Pprint.arbitrary_string msg];
      issue_range = range;
      issue_number = number;
      issue_ctx = ctx }
