module StableErr

(* Checking that error number #298 is stable, so indirectly checking
 * those with a smaller number too. If this throws a different error DO
 * NOT CHANGE THIS FILE. It's likely an error was added to the middle
 * of FStar.Errors instead of appending it, and that's what should be
 * fixed. *)

#set-options "--no_smt"
[@(expect_failure [298])]
let _ = assert False
