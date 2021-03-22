module Bug2257

open FStar.Tactics

let match_sigelt (n: name) =
  let se = lookup_typ (top_env ()) n in
  match se with | Some _ -> ()
                | None -> ()

val foo: int
let _ = run_tactic (fun _ -> match_sigelt ["SigeltVal";"foo"])
