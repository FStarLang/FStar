module Bug1154_tactic

open FStar.Tactics

let app (t: tactic unit): tactic unit =
  seq idtac t
