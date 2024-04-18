module TestMisc

module U32 = FStar.UInt32

#set-options "--no_smt"

let _ = assert_norm (UInt.size 0 32)
let _ = assert_norm (UInt.size 1 32)
let _ = assert_norm (UInt.size 4294967295 32)

[@@expect_failure]
let _ = assert_norm (UInt.size 4294967296 32)

let main () : FStar.All.ML unit = ()
