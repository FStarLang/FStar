module Aliens

open FStar.Tactics

(* Testing that aliens are typechecked/unquoted properly *)

let test =
  assert_by_tactic (True ==> True)
    (b <-- implies_intro;
     qb <-- quote b;
     qf <-- quote (fun (b: binder) -> print "f"); // f: tactic unit
     let q_fofb = mk_app qf [(qb, Q_Explicit)] in
     print ("::: " ^ term_to_string q_fofb);;
     tac <-- unquote #(tactic unit) q_fofb;
     tac;;
     trivial)
