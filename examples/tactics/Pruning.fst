module Pruning

(* Testing namespace pruning. Should check the Z3 query to see if it works. *)

open FStar.Tactics
open FStar.List

let _ = assert_by_tactic (prune [];;
                          addns ["FStar";"List"];;
                          addns ["Prims"]) (rev [1;2] == [2;1])
