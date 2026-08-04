(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
   Author: Brian Milnes <briangmilnes@gmail.com>

*)

///  Some of these tests are marked with expect_failure as they won't run at
/// validation time given an interface file for operations. There is run -time
/// test code for them in another FStar.String.TestMain. Which at this point
/// only prints.
/// 

module Test.FStar.String

open FStar.String

open FStar.String
open FStar.String.Base
open FStar.String.Properties
open FStar.String.Match
open FStar.Class.Printable

///   Is this caused by strlen being UTF8 characters instead of bytes?
///  And there is no byte length.
let _ = assert_norm(strlen "A" = 1)
let _ = assert(streq_upto "A" "AB" 0)
let _ = assert(streq_upto "AB" "AB" 0)

let _ = assert_norm(streq_upto "AB" "AB" 1)
let _ = assert_norm(streq_upto "AB" "AB" 2)

[@@expect_failure]
let _ = assert_norm(lines "" 0 = (0,0))

[@@expect_failure]
let _ = assert_norm(lines "A" 0 = (0,0))
let _ = assert_norm(strlen "A" = 1)

let strlen_A_1 () : Lemma (strlen "A" = 1) = assert_norm(strlen "A" = 1)

[@@expect_failure]
let _ = assert_norm(strlen_A_1(); lines "A" 1 = (0,1))

[@@expect_failure]
let _ = assert_norm(strlen "A\n" = 2);
        assert_norm(lines "A\n" 1 = (0,1))

[@@expect_failure]
let _ = assert_norm(strlen "AB\nC\nD" = 6);
        assert_norm(lines  "AB\nC\nD" 0 = (0,0))

[@@expect_failure]
let _ = assert_norm(strlen "AB\nC\nD" = 6);
        assert_norm(lines  "AB\nC\nD" 1 = (0,1))

[@@expect_failure]
let _ = assert_norm(strlen "AB\nC\nD" = 6);
        assert_norm(lines  "AB\nC\nD" 2 = (0,2))

[@@expect_failure]
let _ = assert_norm(strlen "AB\nC\nD" = 6);
        assert_norm(lines  "AB\nC\nD" 3 = (1,0))

[@@expect_failure]
let _ = assert_norm(strlen "AB\nC\nD" = 6);
        assert_norm(lines  "AB\nC\nD" 4 = (1,1))

[@@expect_failure]
let _ = assert_norm(strlen "AB\nC\nD" = 6);
        assert_norm(lines  "AB\nC\nD" 5 = (2,0))

[@@expect_failure]
let _ = assert_norm(strlen "AB\nC\nD" = 6);
        assert_norm(lines  "AB\nC\nD" 6 = (2,1))

/// A few streq_uptos 
let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(streq_upto "ABCDEF" "ABCDEF" 0)

let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(streq_upto "ABCDEF" "ABCDEF" 1)

let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(streq_upto "ABCDEF" "ABCDEF" 6)

let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(streq_upto "ABCDEF" "ABCDEF" 6)

let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(~(streq_upto "ABCDEF" "ABC" 6))

/// A few streq_upto'
let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(streq_upto' "ABCDEF" "ABCDEF" 0)

let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(streq_upto' "ABCDEF" "ABCDEF" 1)

let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(streq_upto' "ABCDEF" "ABCDEF" 6)

let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(streq_upto' "ABCDEF" "ABCDEF" 6)

[@@expect_failure]
let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(strlen "ABC123" = 6);
        assert_norm(streq_upto' "ABCDEF" "ABC123" 1)

[@@expect_failure]
let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(strlen "ABC123" = 6);
        assert_norm(streq_upto' "ABCDEF" "ABC123" 2)
[@@expect_failure]
let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(strlen "ABC123" = 6);
        assert_norm(streq_upto' "ABCDEF" "ABC123" 3)

[@@expect_failure]
let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(strlen "ABC123" = 6);
        assert_norm(~(streq_upto' "ABCDEF" "ABC123" 4))

[@@expect_failure]
let _ = assert_norm(strlen "ABCDEF" = 6);
        assert_norm(strlen "ABC123" = 6);
        assert_norm(~(streq_upto' "ABCDEF" "ABC123" 5))
