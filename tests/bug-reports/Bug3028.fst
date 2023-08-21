module Bug3028

let mk t = unit -> Dv t
let mk2 t = mk t

let _ = assert (mk int == mk2 int)

[@@expect_failure]
let _ = assert (mk int == mk bool)

[@@expect_failure]
let _ = assert (mk int == mk2 bool)

let mka (x:int) : unit -> Dv int = fun () -> x

[@@expect_failure]
let test () =
  assert (mka 1 == mka 2)
