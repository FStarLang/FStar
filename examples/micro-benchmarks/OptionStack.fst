module OptionStack

[@fail]
let _ = assert False

#push-options "--admit_smt_queries true"

let _ = assert False

#pop-options

[@fail]
let _ = assert False
