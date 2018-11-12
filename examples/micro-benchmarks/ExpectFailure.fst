module ExpectFailure

(* Checking that the definition fails *)
[@ expect_failure]
let _ = 1 + 'a'

(* Checking that it raises one specific error code, and no others *)
[@ (expect_failure [189])]
let _ = 1 + 'a'

(* Same semantics for verification errors *)
[@ expect_failure]
let _ = assert False
[@ (expect_failure [19])]
let _ = assert False

(* Now for interaction with --lax *)
#set-options "--lax"

(* These are ignored, since we're laxing and using the ordinary `expect_failure` *)
[@expect_failure]
let _ = assert False
[@expect_failure]
let _ = assert True

(* We can use expect_lax_failure to ask for a lax-checking failure *)
[@expect_lax_failure]
let _ = 1 + 'a'

#reset-options ""

(* Expecting a lax failure can be done without --lax too, the flag
 * will be internally set when `expect_lax_failure` is specified. *)
[@expect_lax_failure]
let _ = 1 + 'a'

(* These two would fail (to fail :) ), since they lax-check correctly *)
//[@expect_lax_failure]
//let _ = assert False
//
//[@expect_lax_failure]
//let _ = assert True

(* We can also specify the expected errors *)
[@ (expect_lax_failure [189])]
let _ = 1 + 'a'
