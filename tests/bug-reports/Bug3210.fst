module Bug3210

module Tac = FStar.Tactics

let lift_ty: Tac.term -> Tac.Tac Tac.term =
  let rec go (t: Tac.term): Tac.Tac Tac.term =
    t
  in Tac.visit_tm go

[@@Tac.preprocess_with lift_ty]
let rec count (x: int): int =
  if x > 0 then count (x - 1) else 0
