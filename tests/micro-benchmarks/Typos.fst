module Typos

// open FStar.Tactics.TypeClasses

[@@expect_failure]
let x = Proms.solve

[@@expect_failure]
let x = Prims.strong

let a = 1
let b = 2
let c = 3

[@@expect_failure]
let _ = d

module Foooo1 = Prims
module Foooo2 = Prims

[@@expect_failure]
let x = Foooo3.string
