module Bug1506
[@expect_failure [185]]
type single_or_tuple (t1:Type0) (t2:Type0) =
  | S: t1
  | T: t1*t2
