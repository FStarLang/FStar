(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Canon.Test
module XX = FStar.Tactics.Canon // load it, to get the symbols for the lemmas
open FStar.Tactics
open FStar.Mul
open Canon

assume val x : int
assume val y : int
assume val z : int

let lem0 = assert (x * (y * z) == (x * y) * z) by check_canon ()

// TODO: for now, canon is not enough as we don't collect factors
let lem1 =
    assert ((x + y) * (z + z) == 2 * z * (y + x))
        by canon ()

let lem2 (x : int) =
    assert (2 + x + 3 * 8 == x + 26) by check_canon ()

let lem3 (a b c d e : int) =
    assert (c + (b + a) == b + (a + c)) by check_canon ()

let lem4 (a b c : int) =
    assert ((a+c+b)*(b+c+a) == a * a + (((b+c)*(c+b) + a * (b+c)) + c*a) + b*a) by check_canon ()

let lem5 (a b c d e : int) =
    assert
        ((a+b+c+d+e)*(a+b+c+d+e) ==
                a * a + a * b + a * c + a * d + a * e
              + b * a + b * b + b * c + b * d + b * e
              + c * a + c * b + c * c + c * d + c * e
              + d * a + d * b + d * c + d * d + d * e
              + e * a + e * b + e * c + e * d + e * e)
        by check_canon ()

let lem6 (a b c d e : int) =
    assert
        ((a+b+c+d+e)*(e+d+c+b+a) ==
                a * a + a * b + a * c + a * d + a * e
              + b * a + b * b + b * c + b * d + b * e
              + c * a + c * b + c * c + c * d + c * e
              + d * a + d * b + d * c + d * d + d * e
              + e * a + e * b + e * c + e * d + e * e)
        by check_canon ()

let lem7 (a b c d : int) =
    assert
        ((a+b+c+d)*(b+c+d+a) ==
                a * a
              + b * b
              + c * c
              + d * d
              + a * b + a * b
              + a * c + a * c
              + a * d + a * d
              + b * c + b * c
              + b * d + b * d
              + c * d + c * d)
        by check_canon ()

let lem8 (a b c d : int) =
    assert_norm (1 * 1 == 1);
    assert ((a * b) * (c * d) == d * b * c * a)
        by check_canon ()

let lem9 (n:int) (p:int) (r:int) (h:int) (r0:int) (r1:int) (h0:int) (h1:int) (h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int) =
    assert (((h2 * (n * n) + h1 * n + h0) * (r1*n + r0)) =
    ((h2 * r1) * (n * n * n) + (h2 * r0 + h1 * r1) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0))
        by check_canon ()

let lem10 (a b c : int) (n:int) (p:int) (r:int) (h:int) (r0:int) (r1:int) (h0:int) (h1:int) (h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int) =
    assert ((((h2 * (n * n) + h1 * n + h0) * (r1*n + r0))) * ((a+b+c)*(a+b+c)) =
    (((h2 * r1) * (n * n * n) + (h2 * r0 + h1 * r1) * (n * n) + (h1 * r0 + h0 * r1) * n + h0 * r0))
    * (a * a + a * b + a * c +  b * a + b * b + b * c + c * a + c * b + c * c))
        by check_canon ()
