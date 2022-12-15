module UnicodeOperators

open FStar.Tactics

// Unicode symbols that belongs to the 
// [Math Symbol](compart.com/unicode/category/sm)
// category can be used as right associative binary operators.

let ( ∈ ) = List.Tot.memP
let ( ⊆ ) (l1 l2: list 'a): Type0 = forall x. x ∈ l1 ==> x ∈ l2

let _ = assert_norm (3 ∈ [1;2;3;4])
let _ = assert_norm ([2;4] ⊆ [1;2;3;4])

assume val ( ⊕ ): int -> int -> int
let _ = run_tactic (fun _ ->
  guard (term_to_string (`(1 ⊕ 2)) = "1 ⊕ 2")
)
