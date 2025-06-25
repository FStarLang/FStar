module NoInlineLet
open FStar.Tactics

let test_no_inline (f: int): int =
  (* this one shouldn't be inlined in tactics or extraction *)
  [@@no_inline_let]
  let x = f + 1 in
  (* this one will be inlined by the norm tactic in the below test *)
  let y = x + 2 in
  y + y

[@@(postprocess_with (fun _ -> norm [delta_only [`%test_no_inline]]; trefl ()))]
let test_postprocess (f: int): int =
  let x = test_no_inline f in
  x
