module Bug1482

#set-options "--no_smt"
let _ = assert_norm (1 = 1)
let _ = assert_norm (1 == 1)
let _ = assert_norm (1 === 1)
