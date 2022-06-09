module Bug2597

open FStar.Reflection
open FStar.Tactics

let _ = run_tactic (fun () ->
  let ascribed_return: match_returns_ascription = (fresh_binder (`int), (Inl (`int), None, false)) in
  let _ = pack (Tv_Match (`0) (Some ascribed_return) [Pat_Constant (C_Int 0), (`0)]) in
  ()
)
