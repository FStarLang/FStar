module Bug2565

let test_annot (#a:Type0) (x:int) = ()

// An unresolved implicit in a field attribute must produce an ordinary
// inference error, not a CheckNoUvars assertion failure.
[@@expect_failure [66]]
type test_type = {
  [@@@ test_annot 1337]
  x: int;
}

type annotated_type = {
  [@@@ test_annot #int 1337]
  x: int;
}
