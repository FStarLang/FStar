module MultiStage

open FStar.Tactics

let tau1 () : Tac unit =
  let se = pack_sigelt (Sg_Let false (pack_fv (cur_module () @ ["test1"])) []
                               (`int)
                               (`(synth (fun () -> dump "Running inner tactic 1"; exact (`42))))) in
  exact (quote [se])

%splice[test1] (tau1 ())

let _ = assert (test1 == 42)

let tau2 () : Tac unit =
  let res : term = quote 42 in
  let se = pack_sigelt (Sg_Let false (pack_fv (cur_module () @ ["test2"])) []
                               (`int)
                               (`(synth (fun () -> dump "Running inner tactic 2"; exact (`@res))))) in
  exact (quote [se])


  
%splice[test2] (tau2 ())

let _ = assert (test2 == 42)
