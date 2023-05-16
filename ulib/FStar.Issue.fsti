module FStar.Issue
open FStar.Range

new
val issue : Type0

let issue_level_string = s:string {
  s == "Info" \/
  s == "Warning" \/
  s == "Error" \/
  s == "Feature not yet implemented: "
}

val message_of_issue (i:issue) : Tot string

val level_of_issue (i:issue) : Tot issue_level_string

val number_of_issue (i:issue) : Tot (option int)

val range_of_issue (i:issue) : Tot (option range)

val context_of_issue (i:issue) : Tot (list string)
  
val mk_issue (i:issue_level_string)
             (msg:string)
             (range:option range)
             (number:option int)
             (ctx:list string)
  : Tot issue
