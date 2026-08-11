module TestMBQI
#set-options "--z3smtopt '(set-option :smt.mbqi true)'"
[@@expect_failure [19]]
let test () : squash False = ()