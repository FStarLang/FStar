module Bug2522

[@@ expect_failure [185]]
type test_type (t:Type0) {| unit |} =
  | A : int

/// Bug#2570

[@@ expect_failure [185]]
type test (t:Type0) =
  | Test : unit
