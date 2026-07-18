module InterleaveDupException

// This should fail due to a duplicate definition of an exception
[@@expect_failure [47]]
exception MyExn
