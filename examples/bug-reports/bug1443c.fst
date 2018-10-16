module Bug1443c

val foo : unit -> unit

[@(expect_failure [66])]
let foo t =
  let rec bar env t = ()
  in bar [] t
