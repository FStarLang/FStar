module Bug1956

[@expect_failure]
let xx : squash False = ()

// This can succeed if `xx` leaks into the SMT context for this query
[@expect_failure]
let _ = assert False
