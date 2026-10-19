module Bug4586

(* The implicit of (=) and (==) is marked [@@@unrefine]: it is solved to
   the unrefined type even when the left operand has a refined type,
   including one that comes from a Pure postcondition. *)
assume val f : unit -> Pure int (requires True) (ensures fun r -> r > 0)
let test_pure (y: int) : bool = f () = (y <: _)

assume val g : unit -> Tot (r:int{r > 0})
let test_tot (y: int) : bool = g () = (y <: _)
let test_neq (y: int) : bool = g () <> (y <: _)
let test_eq2 (y: int) : prop = g () == (y <: _)

(* Abbreviations are kept: this equality is at nat. *)
let test_abbrev (n: nat) (y: nat) : bool = n = y
[@@expect_failure [19]]
let test_abbrev_fail (n: nat) (y: int) : bool = n = (y <: _)
