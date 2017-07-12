module Bug258

noeq type value : Type0 =
  | V_clos : env -> nat -> value
and env = | E: f:(nat -> Tot value) -> env

assume val pr_axiom: en:env -> x:nat -> Lemma (ensures (en.f x << en))

val slice_v : v:value -> Tot value //(decreases v) // Works with this clause

val slice_en: en:env -> n:nat -> Tot value (decreases en)

let rec slice_v v = match v with
  | V_clos en x ->
    V_clos (E (slice_en en)) x
and slice_en en y = pr_axiom en y; slice_v (en.f y)
