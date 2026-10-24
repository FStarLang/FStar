module Bug2359

// Mixing an explicit universe with a generalized one must report a typing
// error, rather than an assertion failure about an unbound universe name.
[@@expect_failure [191]]
let example _ = Type u#a -> Type

let explicit_universes (_:unit) = Type u#a -> Type u#a
