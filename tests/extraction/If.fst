module If

#push-options "--admit_smt_queries true"
let test (x:bool) : int =
  match x with
  | true when false -> 10
  | _ -> 20
#pop-options

let x = test true
let _ = assert (x == 20)
