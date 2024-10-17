module Test.FStar.String

open FStar.String
open FStar.Tactics.V2
open FStar.IO


open FStar.String
open FStar.Class.Printable

let _ = assert(streq "" "")
let _ = assert(streq "A" "A")

///   Is this caused by strlen being UTF8 characters instead of bytes?
///  And there is no byte length.
let _ = assert(strlen "A" = 1) by compute()
let _ = assert(~(streq "A" "AB")) by compute()
let _ = assert(streq_upto "A" "AB" 0)
let _ = assert(streq_upto "AB" "AB" 0)

[@@expect_failure]
let _ = assert(streq_upto "AB" "AB" 1)

let _ = assert(streq_upto "AB" "AB" 1) by compute()

[@@expect_failure]
let _ = assert(streq_upto "AB" "AB" 2)
let _ = assert(streq_upto "AB" "AB" 2) by compute()

[@@expect_failure]
let _ = assert(~ (streq "A" "B"))
let _ = assert(~(streq "A" "AB")) by compute()
[@@expect_failure]
let _ = assert(~(streq "AB" "Ab")) by compute()

///  The boolean form is hidden behind the interface.
[@@expect_failure]
let _ = assert(~ (streq "A" "B")) by compute()
let _ = assert(streq' "" "") by compute()
[@@expect_failure]
let _ = assert(not (streq' "" "A")) by compute()


/// Of course by compute can't prove things it can't see a definition on.
/// So once you hide it behind an interface it can't run it.
/// So I need a test module but this goes in before Final so no tests yet.
[@@expect_failure]
let _ = assert(lines "" 0 = (0,0))  by compute()

[@@expect_failure]
let _ = assert(lines "A" 0 = (0,0)) by compute()
let _ = assert(strlen "A" = 1)      by compute()

let strlen_A_1 () : Lemma (strlen "A" = 1) = assert(strlen "A" = 1) by compute()
[@@expect_failure]
let _ = assert(strlen_A_1(); lines "A" 1 = (0,1)) by compute()

[@@expect_failure]
let _ = assert(strlen "A\n" = 2) by compute();
        assert(lines "A\n" 1 = (0,1)) by compute()

[@@expect_failure]
let _ = assert(strlen "AB\nC\nD" = 6) by compute();
        assert(lines  "AB\nC\nD" 0 = (0,0)) by compute()

[@@expect_failure]
let _ = assert(strlen "AB\nC\nD" = 6) by compute();
        assert(lines  "AB\nC\nD" 1 = (0,1)) by compute()

[@@expect_failure]
let _ = assert(strlen "AB\nC\nD" = 6) by compute();
        assert(lines  "AB\nC\nD" 2 = (0,2)) by compute()

[@@expect_failure]
let _ = assert(strlen "AB\nC\nD" = 6) by compute();
        assert(lines  "AB\nC\nD" 3 = (1,0)) by compute()

[@@expect_failure]
let _ = assert(strlen "AB\nC\nD" = 6) by compute();
        assert(lines  "AB\nC\nD" 4 = (1,1)) by compute()

[@@expect_failure]
let _ = assert(strlen "AB\nC\nD" = 6) by compute();
        assert(lines  "AB\nC\nD" 5 = (2,0)) by compute()

[@@expect_failure]
let _ = assert(strlen "AB\nC\nD" = 6) by compute();
        assert(lines  "AB\nC\nD" 6 = (2,1)) by compute()

