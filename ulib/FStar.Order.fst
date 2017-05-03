module FStar.Order

type order = | Lt | Eq | Gt

// Some derived checks
val ge : order -> bool
let ge o = o <> Lt

val le : order -> bool
let le o = o <> Gt

val ne : order -> bool
let ne o = o <> Eq

// Just for completeness and consistency...
val gt : order -> bool
let gt o = o = Gt

val lt : order -> bool
let lt o = o = Lt

val eq : order -> bool
let eq o = o = Eq
