module Fail

[@ fail]
let _ = 1 + 'a'

[@ (fail_errs [189])]
let _ = 1 + 'a'

[@ fail]
let _ = assert False

[@ (fail_errs [19])]
let _ = assert False
