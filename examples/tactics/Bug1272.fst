module Bug1272

open FStar.Tactics

#set-options "--admit_smt_queries true"

let unsquash #a : a -> squash a =
  fun _ -> ()

let broken (a: Type0) =
  assert_by_tactic a (fun () ->
                        apply (quote (unsquash #a));
                        let xx : a = admit () in
                        exact (quote xx))

let yy : (Type0 -> unit) =
  synth_by_tactic (fun () -> exact (norm_term [] (quote broken)))

let _ =
  assert_by_tactic True
                   (fun () ->
                     admit ();
                     let x = quote 1 in
                     debug (term_to_string (norm_term [] x)))
