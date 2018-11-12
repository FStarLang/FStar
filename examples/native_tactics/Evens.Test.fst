module Evens.Test
open Evens
open FStar.Tactics

#set-options "--__temp_fast_implicits"
let even_test () =
 assert_by_tactic (even (normalize_term (nat2unary 1024)))
                  prove_even
