module TypingFactsGuards

(* The SMT encoding states the result type of pure applications as ground
   hypotheses (issue #4591).  An application under a guard is only well typed
   under that guard, so its typing must not be stated outside of it: otherwise
   each of these would prove [x >= 0] from [g x <= x] and [g x >= 0]. *)

assume val g : x:int{x >= 0} -> r:nat{r <= x}
assume val p : int -> prop

assume val lem_imp (x:int) : Lemma (x >= 0 ==> p (g x))
assume val lem_or  (x:int) : Lemma (x < 0 \/ p (g x))
assume val lem_and (x:int) : Lemma ((x >= 0 && g x = 1) || true)
assume val lem_ite (x:int) : Lemma (if x >= 0 then p (g x) else True)

[@@expect_failure [19]]
let via_imp (x:int) : Lemma (x >= 0) = lem_imp x

[@@expect_failure [19]]
let via_or (x:int) : Lemma (x >= 0) = lem_or x

[@@expect_failure [19]]
let via_and (x:int) : Lemma (x >= 0) = lem_and x

[@@expect_failure [19]]
let via_ite (x:int) : Lemma (x >= 0) = lem_ite x

(* Where the application is not guarded, its typing is available. *)
assume val lem_plain (x:int{x >= 0}) : Lemma (p (g x))

let plain (x:int{x >= 0}) : Lemma (g x <= x) = lem_plain x
