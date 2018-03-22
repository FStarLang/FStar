module Antiquote

open FStar.Tactics

let _ = assert_by_tactic True
            (fun () -> let tm = (`(1 + `@(1))) in
                       let z = 16 in
                       let x = `16 in
                       let tm2 = `(1 + `@(z)) in
                       let tm3 = `(1 + `#(x)) in
                       print ("tm = " ^ term_to_string tm);
                       print ("tm2 = " ^ term_to_string tm2);
                       print ("tm3 = " ^ term_to_string tm3);
                       let ty = tc tm in
                       print ("ty = " ^ term_to_string ty);
                       let ty2 = tc tm2 in
                       print ("ty2 = " ^ term_to_string ty2);
                       let ty3 = tc tm3 in
                       print ("ty3 = " ^ term_to_string ty3);
                       ())

(* TODO: When --use_extracted_interfaces is given, if we do
 * ignore (tc tm), the tactics get stuck. Investigate. *)

let _ = assert_by_tactic True
            (fun () -> let y = True in
                       let tm = `(False ==> `@y) in
                       print ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = bool in
                       let tm = `(int * (`@y)) in
                       print ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `((+) (`@y) 25) in
                       print ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())


let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `(fun z -> z + (`@y)) in
                       print ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `(if (`@y) = 22 then (`@y) - 1 else 1 - (`@y)) in
                       print ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `(match (`@y) with | 4 -> 1 + (`@y) | _ -> 99) in
                       print ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())
