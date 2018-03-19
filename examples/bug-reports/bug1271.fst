module Bug1271

open FStar.Tactics

let test =
  assert_by_tactic (True ==> True)
    (fun () -> let b = implies_intro () in
               let qb = quote b in
               let qf = quote (fun (b: binder) () -> print "f") in // f: tactic unit
               let q_fofb = mk_app qf [(qb, Q_Explicit)] in
               print ("::: " ^ term_to_string q_fofb);
               let tac = unquote #(unit -> Tac unit) q_fofb in
               tac ();
               trivial ())
