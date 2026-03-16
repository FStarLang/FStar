module AutoPatternsWarn

(* Test that pattern inference failure emits a warning.
   Run with --ext auto_patterns
   Warning code 271 = Warning_SMTPatternIllFormed *)

assume val f : int -> int

(* This needs a conjunctive pattern {:pattern (f x); (f y)} which we don't support.
   Should emit Warning_SMTPatternIllFormed (243). *)
assume val ax_fail : squash (forall (x:int) (y:int). f x == f y)
