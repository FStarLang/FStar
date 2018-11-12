module Bug1348

val coerce_eq2 : a:(nat -> Type) -> b:(nat -> Type){a 0 == b 0} -> a 0 -> b 0
let coerce_eq2 a b v = v
