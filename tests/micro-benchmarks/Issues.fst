module Issues
open FStar.Issue
module T = FStar.Tactics
// (* This test exercises the reflection of FStar.Issue *)

let print_issue (i:issue) : string = message_of_issue i
let sample_range = range_of print_issue
let test_issue = mk_issue "Error" "Test" (Some sample_range)
                          (Some 17) ["this"; "context"]
let test = 
  assert (message_of_issue test_issue == "Test")
    by T.(compute(); trefl(); qed());
  assert (level_of_issue test_issue == "Error")
    by T.(compute(); trefl(); qed());
  assert (range_of_issue test_issue == (Some sample_range))
    by T.(compute(); trefl(); qed());
  assert (number_of_issue test_issue == (Some 17))
    by T.(compute(); trefl(); qed());
  assert (context_of_issue test_issue == ["this"; "context"])
    by T.(compute(); trefl(); qed())    
