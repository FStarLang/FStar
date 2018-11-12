module Labels

open FStar.Tactics

let _ = assert ((1 == 1)/\ (True /\ True)) by (explode (); iseq [(fun () -> tlabel "Left"); (fun () -> tlabel "Right")]; dump "dump msg")
