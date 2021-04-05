module Bug855a

open FStar.Ref

val bar: unit -> St (unit -> St nat)
let bar () =
  let r = alloc 2 in
  let f:(unit -> St nat) = fun () -> !r in
  f
