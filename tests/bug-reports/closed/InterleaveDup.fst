module InterleaveDup

// This should fail due to a duplicate definition
[@@expect_failure [47]]
let x = 1

// This should fail due to prove the assertion
[@@expect_failure [19]]
let lem () = ()
