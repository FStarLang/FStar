module OptionStack

[@expect_failure]
let _ = assert False

#push-options "--admit_smt_queries true"

let _ = assert False

#pop-options

[@expect_failure]
let _ = assert False
