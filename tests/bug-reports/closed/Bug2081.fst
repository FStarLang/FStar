module Bug2081

open FStar.Tactics.V2

let pp_test () : Tac unit = trefl()

[@(postprocess_with pp_test)]
let test () =
  admit()
