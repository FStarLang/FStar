module Phase2CoreLemmaPatterns

(* With --ext phase2_core, phase 1's elaboration of a declaration is kept, so
   the unification variables in the SMT pattern of a lemma type must be
   removed from it like everywhere else (they were not, and checking the
   projector of C failed with Error 334, "incompatible version for universe
   unification variable"). *)
noeq type t = | C : (x:int -> Lemma (x + 1 > x) [SMTPat (Some x)]) -> t

let use (c:t) (x:int) : Lemma (x + 1 > x) = let C f = c in f x

(* Core does not check SMT patterns: the warnings TcTerm emits for them in its
   phase 2 are emitted for terms checked by Core too. *)
#push-options "--warn_error @271"
[@@expect_failure [271]]
assume val lem_val (x:int) (y:int) : Lemma (x + 1 > x) [SMTPat (Some x)]

[@@expect_failure [271]]
let lem_arg (f : (x:int -> y:int -> Lemma (x + 1 > x) [SMTPat (Some x)])) : unit = ()

[@@expect_failure [271]]
assume val lem_theory (x:int) : Lemma (x + 1 > x) [SMTPat (x + 1)]
#pop-options
