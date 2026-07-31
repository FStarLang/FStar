module IfaceNoPragmaLeak

(* The interface's [#push-options "--admit_smt_queries true"] does not carry
   over to the implementation, so this query is not admitted. *)
let f (x:int) : nat = x
