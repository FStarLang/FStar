module WeakVsHNF

open FStar.Tactics

// TODO: actually make this a regression test which fails when things go wrong

(* Testing weak reduction vs. HNF *)

let _ = assert_by_tactic True
        (t0 <-- quote (1 + 1);
         print "";;
         print ("Term  :  " ^ term_to_string t0);;
         t <-- norm_term [primops] t0;
         print ("Full  :  " ^ term_to_string t);;
         t <-- norm_term [primops; weak] t0;
         print ("Weak  :  " ^ term_to_string t);;
         t <-- norm_term [primops; hnf] t0;
         print ("HNF   :  " ^ term_to_string t);;
         t <-- norm_term [primops; weak; hnf] t0;
         print ("WHNF  :  " ^ term_to_string t))

let _ = assert_by_tactic True
        (t0 <-- quote (fun () -> 1 + 1);
         print "";;
         print ("Term  :  " ^ term_to_string t0);;
         t <-- norm_term [primops] t0;
         print ("Full  :  " ^ term_to_string t);;
         t <-- norm_term [primops; weak] t0;
         print ("Weak  :  " ^ term_to_string t);;
         t <-- norm_term [primops; hnf] t0;
         print ("HNF   :  " ^ term_to_string t);;
         t <-- norm_term [primops; weak; hnf] t0;
         print ("WHNF  :  " ^ term_to_string t))

let _ = assert_by_tactic True
        (t0 <-- quote (op_Addition (1 + 1));
         print "";;
         print ("Term  :  " ^ term_to_string t0);;
         t <-- norm_term [primops] t0;
         print ("Full  :  " ^ term_to_string t);;
         t <-- norm_term [primops; weak] t0;
         print ("Weak  :  " ^ term_to_string t);;
         t <-- norm_term [primops; hnf] t0;
         print ("HNF   :  " ^ term_to_string t);;
         t <-- norm_term [primops; weak; hnf] t0;
         print ("WHNF  :  " ^ term_to_string t))

let _ = assert_by_tactic True
        (t0 <-- quote (fun () -> (fun x -> x) 2);
         print "";;
         print ("Term  :  " ^ term_to_string t0);;
         t <-- norm_term [primops] t0;
         print ("Full  :  " ^ term_to_string t);;
         t <-- norm_term [primops; weak] t0;
         print ("Weak  :  " ^ term_to_string t);;
         t <-- norm_term [primops; hnf] t0;
         print ("HNF   :  " ^ term_to_string t);;
         t <-- norm_term [primops; weak; hnf] t0;
         print ("WHNF  :  " ^ term_to_string t))
