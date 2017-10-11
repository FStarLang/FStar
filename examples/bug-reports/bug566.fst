module Bug566

// Fails with "Mutually defined type contains a non-inductive element"
type value =
  | C: nat -> value
  | F: env value -> value
and env = nat -> Tot value

// A workaround
type env value = nat -> Tot value
noeq type value =
 | C: nat -> value
 | F: env value -> value
