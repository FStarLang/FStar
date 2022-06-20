module Bug2471_B

open Bug2471_A
open FStar.Tactics

let _ = run_tactic (fun _ -> let _ = implicit1 () in ())
let _ = run_tactic (fun _ -> let _ = implicit2 () in ())

let _ = run_tactic (fun _ -> let _ = implicit3 () in ())
let _ = run_tactic (fun _ -> let _ = implicit4 () in ())
let _ = run_tactic (fun _ -> let _ = explicit1 () in ())
let _ = run_tactic (fun _ -> let _ = explicit2 () in ())
