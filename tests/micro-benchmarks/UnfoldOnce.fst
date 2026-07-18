module UnfoldOnce

open FStar.Tactics.V2

#push-options "--admit_smt_queries true"
let rec f () : Tot int = 1 + f ()
#pop-options

let _ =
  assert True by begin
    let t = (`(f ())) in
    let t' = norm_term [delta_once [`%f]] t in
    let expected = (`(1 + f () <: Tot Prims.int)) in
    (* print ("t' = " ^term_to_string t'); *)
    (* print ("expected = " ^term_to_string expected); *)
    guard (term_eq t' expected);
    ()
  end

let _ =
  assert True by begin
    let t = (`(f () + f ())) in
    let t' = norm_term [delta_once [`%f]] t in
    let expected = (`((1 + f () <: Tot Prims.int) + f ())) in
    (* print ("t' = " ^term_to_string t'); *)
    (* print ("expected = " ^term_to_string expected); *)
    guard (term_eq t' expected);
    ()
  end
