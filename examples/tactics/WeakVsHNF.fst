module WeakVsHNF

open FStar.Tactics

// TODO: actually make this a regression test which fails when things go wrong

(* Testing weak reduction vs. HNF *)

let _ = assert_by_tactic True
        (fun () ->
             let t0 = `(1 + 1) in
             print "";
             print ("Term  :  " ^ term_to_string t0);
             let t = norm_term [primops] t0 in
             print ("Full  :  " ^ term_to_string t);
             let t = norm_term [primops; weak] t0 in
             print ("Weak  :  " ^ term_to_string t);
             let t = norm_term [primops; hnf] t0 in
             print ("HNF   :  " ^ term_to_string t);
             let t = norm_term [primops; weak; hnf] t0 in
             print ("WHNF  :  " ^ term_to_string t))

let _ = assert_by_tactic True
        (fun () ->
             let t0 = `(fun () -> 1 + 1) in
             print "";
             print ("Term  :  " ^ term_to_string t0);
             let t = norm_term [primops] t0 in
             print ("Full  :  " ^ term_to_string t);
             let t = norm_term [primops; weak] t0 in
             print ("Weak  :  " ^ term_to_string t);
             let t = norm_term [primops; hnf] t0 in
             print ("HNF   :  " ^ term_to_string t);
             let t = norm_term [primops; weak; hnf] t0 in
             print ("WHNF  :  " ^ term_to_string t))

let _ = assert_by_tactic True
        (fun () ->
             let t0 = `(op_Addition (1 + 1)) in
             print "";
             print ("Term  :  " ^ term_to_string t0);
             let t = norm_term [primops] t0 in
             print ("Full  :  " ^ term_to_string t);
             let t = norm_term [primops; weak] t0 in
             print ("Weak  :  " ^ term_to_string t);
             let t = norm_term [primops; hnf] t0 in
             print ("HNF   :  " ^ term_to_string t);
             let t = norm_term [primops; weak; hnf] t0 in
             print ("WHNF  :  " ^ term_to_string t))

let _ = assert_by_tactic True
        (fun () ->
             let t0 = `(fun () -> (fun x -> x) 2) in
             print "";
             print ("Term  :  " ^ term_to_string t0);
             let t = norm_term [primops] t0 in
             print ("Full  :  " ^ term_to_string t);
             let t = norm_term [primops; weak] t0 in
             print ("Weak  :  " ^ term_to_string t);
             let t = norm_term [primops; hnf] t0 in
             print ("HNF   :  " ^ term_to_string t);
             let t = norm_term [primops; weak; hnf] t0 in
             print ("WHNF  :  " ^ term_to_string t))
