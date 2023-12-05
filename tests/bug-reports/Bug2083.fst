module Bug2083

open FStar.Tactics

let meta_f (x y : option nat) : Tot bool =
  if Some? x && Some? y && Some?.v x = Some?.v y then true
  else false

let pp_tac () : Tac unit =
  let b = meta_f (Some 0) None in
  if b then trefl() else trefl()

[@(postprocess_with pp_tac)]
let test () : bool =
  true
