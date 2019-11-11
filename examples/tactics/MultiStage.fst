module MultiStage

open FStar.Tactics

let tau1 () : Tac decls =
  let se = pack_sigelt (Sg_Let false (pack_fv (cur_module () @ ["test1"])) []
                               (`int)
                               (`(synth (fun () -> dump "Running inner tactic 1"; exact (`42))))) in
  [se]

%splice[test1] (tau1 ())
let _ = assert (test1 == 42)

let tau2 () : Tac decls =
  let res : term = quote 42 in
  let se = pack_sigelt (Sg_Let false (pack_fv (cur_module () @ ["test2"])) []
                               (`int)
                               (`(synth (fun () -> dump "Running inner tactic 2"; exact (`@res))))) in
  [se]

%splice[test2] (tau2 ())
let _ = assert (test2 == 42)

let tau3 () : Tac decls =
  let res : term = quote 42 in
  let se = pack_sigelt (Sg_Let false (pack_fv (cur_module () @ ["test3"])) []
                               (`int)
                               (`(_ by (dump "Running inner tactic 3";
                                        exact (`@res))))) in
  [se]

%splice[test3] (tau3 ())
let _ = assert (test3 == 42)

(* This will get stuck, `res` has no definition in the environment where the tactic runs *)
(* let tau4 () : Tac decls = *)
(*   let se = pack_sigelt (Sg_Let false (pack_fv (cur_module () @ ["test4"])) [] *)
(*                                (`int) *)
(*                                (`(let res : term = quote 42 in *)
(*                                   _ by (dump "Running inner tactic 4"; *)
(*                                         let x = 42 in *)
(*                                         exact (res))))) in *)
(*   [se] *)
(* %splice[test4] (tau4 ()) *)
(* let _ = assert (test4 == 42) *)

let string_of_name = String.concat "."

let tau5 () : Tac decls =
  let res : term = quote 42 in
  let f_name : name = ["a";"b";"c"] in
  let se = pack_sigelt (Sg_Let false (pack_fv (cur_module () @ ["test5"])) []
                               (`int)
                               (`(_ by (dump ("Running inner tactic 5: " ^ (string_of_name (`@f_name)));
                                        let x = 42 in
                                        exact (quote 42))))) in
  [se]
%splice[test5] (tau5 ())
let _ = assert (test5 == 42)
