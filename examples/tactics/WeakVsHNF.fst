module WeakVsHNF

open FStar.Tactics

(* Testing weak reduction vs. HNF *)

// Using the dynamic quote to get the syntax of the guard that failed.
let guard b =
    if b
    then ()
    else fail ("guard failed: " ^ term_to_string (quote b))

let _ = assert_by_tactic True
        (fun () ->
             let t0 = `(1 + 1) in
             debug "";
             debug ("Term  :  " ^ term_to_string t0);

             let t = norm_term [primops] t0 in
             debug ("Full  :  " ^ term_to_string t);
             guard (term_eq t (`2));

             let t = norm_term [primops; weak] t0 in
             debug ("Weak  :  " ^ term_to_string t);
             guard (term_eq t (`2));

             let t = norm_term [primops; hnf] t0 in
             debug ("HNF   :  " ^ term_to_string t);
             guard (term_eq t (`2));

             let t = norm_term [primops; weak; hnf] t0 in
             debug ("WHNF  :  " ^ term_to_string t);
             guard (term_eq t (`2))
        )

let _ = assert_by_tactic True
        (fun () ->
             let t0 = `(fun () -> 1 + 1) in
             debug "";
             debug ("Term  :  " ^ term_to_string t0);

             let t = norm_term [primops] t0 in
             debug ("Full  :  " ^ term_to_string t);
             guard (term_eq t (`(fun () -> 2)));

             let t = norm_term [primops; weak] t0 in
             debug ("Weak  :  " ^ term_to_string t);
             guard (term_eq t (`(fun () -> 1 + 1)));

             let t = norm_term [primops; hnf] t0 in
             debug ("HNF   :  " ^ term_to_string t);
             guard (term_eq t (`(fun () -> 2)));

             let t = norm_term [primops; weak; hnf] t0 in
             debug ("WHNF  :  " ^ term_to_string t);
             guard (term_eq t (`(fun () -> 1 + 1)))
        )

type wint = | W of int

let _ = assert_by_tactic True
        (fun () ->
             let t0 = `(W (1 + 1)) in
             debug "";
             debug ("Term  :  " ^ term_to_string t0);

             let t = norm_term [primops] t0 in
             debug ("Full  :  " ^ term_to_string t);
             guard (term_eq t (`(W 2)));

             let t = norm_term [primops; weak] t0 in
             debug ("Weak  :  " ^ term_to_string t);
             guard (term_eq t (`(W 2)));

             let t = norm_term [primops; hnf] t0 in
             debug ("HNF   :  " ^ term_to_string t);
             guard (term_eq t (`(W (1 + 1))));

             let t = norm_term [primops; weak; hnf] t0 in
             debug ("WHNF  :  " ^ term_to_string t);
             guard (term_eq t (`(W (1 + 1))))
        )

let _ = assert_by_tactic True
        (fun () ->
             let t0 = `(fun () -> W (1 + 1)) in
             debug "";
             debug ("Term  :  " ^ term_to_string t0);

             let t = norm_term [primops] t0 in
             debug ("Full  :  " ^ term_to_string t);
             guard (term_eq t (`(fun () -> W 2)));

             let t = norm_term [primops; weak] t0 in
             debug ("Weak  :  " ^ term_to_string t);
             guard (term_eq t (`(fun () -> W (1 + 1))));

             let t = norm_term [primops; hnf] t0 in
             debug ("HNF   :  " ^ term_to_string t);
             guard (term_eq t (`(fun () -> W (1 + 1))));

             let t = norm_term [primops; weak; hnf] t0 in
             debug ("WHNF  :  " ^ term_to_string t);
             guard (term_eq t (`(fun () -> W (1 + 1))))
        )
