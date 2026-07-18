(* Test case: nested tuples print strangely in tactic dumps.
  They look OK with --print_in_place though.
  (This isn't strictly an error message test, but it is testing debug
  messages, which are important too.)
*)
module Bug3099

module Tac = FStar.Tactics

let check_print_tuples () =
  assert ((1, (2, (3, 4))) = (1, (2, (3, 4)))) by (Tac.dump "X")
