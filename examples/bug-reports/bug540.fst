module Bug540

[@expect_failure]
let test (a b:Type) =
  let _ =  a = b in
  ()
