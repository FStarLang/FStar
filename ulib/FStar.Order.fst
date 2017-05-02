module FStar.Order

type order = | Lt | Eq | Gt

val ge : order -> bool
let ge o = o <> Lt

val le : order -> bool
let le o = o <> Gt

val ne : order -> bool
let ne o = o <> Eq
