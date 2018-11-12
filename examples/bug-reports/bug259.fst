module Bug259

// this is like a runtime env
type env value = nat -> Tot value

// defining a value datatype
noeq type value =
  | C: nat -> value
  | F: env value -> value

// defining a translation function on values recursively with the translation
// function on env
assume val preceds_axiom: en:env value -> x:nat -> Lemma (ensures (en x << en))

val tr_v : v:value -> Tot value (decreases %[v])
val tr_en: en:env value -> nat -> Tot value (decreases %[en])

let rec tr_v v =
  match v with
    | C n    -> v
    | F en -> F (tr_en en)

and tr_en en x = preceds_axiom en x; tr_v (en x)
//Succeeds using this hack
//
//and tr_en en =
//  let _ = () in
//  fun x -> precedes_axiom en x; tr_v (en x)

// some assumptions
assume val v:value
assume val en:env value
assume val n:nat

// this should succeed
let t = assert (tr_v (F en) == F (tr_en en))
