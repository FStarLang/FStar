module TestMBQI
#set-options "--z3smtopt '(set-option :smt.mbqi true)'"
#set-options "--z3rlimit 100"
[@@expect_failure [19]]
let test () : squash False = ()