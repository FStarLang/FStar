module Bug1305

open FStar.Tactics

let _ =
  assert_by_tactic True
                   (fun () ->
                     admit ();
                     let x = quote 1 in
                     ())
