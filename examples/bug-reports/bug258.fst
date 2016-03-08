module Ast

type value =
  | V_clos : env -> nat -> value

and env =  nat -> Tot value

assume val pr_axiom: en:env -> x:nat -> Lemma (ensures (en x << en))

val slice_v : v:value -> Tot value (decreases v)
(*val slice_v : v:value -> Tot value *) //using this variant causes the proof to fails
val slice_en: en:env -> n:nat -> Tot value (decreases en)

let rec slice_v v = match v with
  | V_clos en x ->
    V_clos (slice_en en) x
and slice_en en y = pr_axiom en y; slice_v (en y)
