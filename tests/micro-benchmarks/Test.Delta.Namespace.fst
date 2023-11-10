module Test.Delta.Namespace
module L = FStar.List.Tot
open FStar.Tactics.V2
module P = FStar.Printf
let f (x:int) = x + 1
let m (y:list int) = L.map f y

let term_eq = FStar.Reflection.V2.TermEq.term_eq

let n2 = assert (m [1;2;3] == L.map (fun x -> x + 1) [1;2;3])
             by (norm [delta_namespace["Test.Delta"];zeta;iota;primops]; //don't unfold the map, but unfold m and f
                 let g = cur_goal () in
                 let tt = (`squash (L.map (fun x -> x+1) [1;2;3] == L.map (fun x -> x+1) [1;2;3])) in
                 let e = cur_env () in
                 match tc_term e tt with
                 | Some (tt, _), _ ->
                   if not (term_eq g tt) then
                     fail ("Unexpected reduction: " ^ term_to_string g ^ "\n\n" ^ term_to_string tt);
                   trefl()
                 | _ ->
                   fail "tc failed"
                 )

(* 'Test.Delt' is not a parent namespace of 'Test.Delta', should not unfold *)
let n3 = assert (m [1;2;3] == L.map (fun x -> x + 1) [1;2;3])
             by (norm [delta_namespace["Test.Delt"];zeta;iota;primops]; //don't unfold the map, but unfold m and f
                 let g = cur_goal () in
                 let tt = (`squash (m [1;2;3] == L.map (fun x -> x+1) [1;2;3])) in
                 let e = cur_env () in
                 match tc_term e tt with
                 | Some (tt, _), _ ->
                   if not (term_eq g tt) then
                     fail ("Unexpected reduction: " ^ term_to_string g ^ "\n\n" ^ term_to_string tt);
                   trefl()
                 | _ ->
                   fail "tc failed"
                 )
