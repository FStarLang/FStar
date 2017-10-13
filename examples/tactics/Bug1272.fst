module Bug1272

open FStar.Tactics

#set-options "--admit_smt_queries true"

let unsquash #a : a -> squash a =
  fun _ -> ()

let broken (a: Type0) =
  assert_by_tactic a (apply (quote (unsquash #a));; let xx : a = admit() in exact (quote xx))

let yy : (Type0 -> unit) =
  synth_by_tactic (fun () -> exact (norm_term [] (quote broken ())) ())
