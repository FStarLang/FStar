module InterleaveDup

// The interface's `let x = 2` must not be dropped, so redefining x here is a
// duplicate definition.
[@@expect_failure [47]]
let x = 1

// ... and the x that is in scope really is 2, not 1.
[@@expect_failure [19]]
let x_is_one () : Lemma (x == 1) = ()

// `lem` is declared by the interface in terms of that same x, so this
// discharges it. (It cannot be attempted under an [@@expect_failure]: such a
// block defines nothing, and `lem` would be left unimplemented.)
let lem () = ()
