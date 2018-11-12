module Bug566

// Fails with "Mutually defined type contains a non-inductive element"
noeq type value =
  | C: nat -> value
  | F: env value -> value
and env value = nat -> Tot value

// A workaround
type env' value' = nat -> Tot value'
noeq type value' =
 | C': nat -> value'
 | F': env' value' -> value'
