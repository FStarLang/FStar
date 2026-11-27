(*
   Copyright 2025 Microsoft Research

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

///
///   This module defines sigma (sum) and pi (product) notation over int and proves some basic
///  theorems about them. 
///

module FStar.SigmaPi
open FStar.IntegerIntervals
open FStar.Mul
open FStar.Math.Lib

///   Sigma is a bit different than you might expect in that there is a fixed outer range
///  x to (y+1) exclusive. This fixed range simplifies many proofs but we provide an
///  Nik produced example of naming lambda literals on the wiki
///  (https://github.com/FStarLang/FStar/wiki/Lambda-Literals-in-SMT-Proof).

///   A sum from i to j of e.
let rec sigma (#x #y: int) 
      (i: interval x (y+1)) (j: interval x (y+1)) 
      (e: interval x (y + 1) -> int):
  Tot int
  (decreases j - i)
=
 if j < i
 then 0
 else if i = j
 then e i
 else sigma i (j - 1) e + e j

val sigma_no_range_is_zero #x #y 
     (i: interval x (y+1)) (j: interval x (y+1){i > j}) 
      (e: interval x (y + 1) -> int):
   Lemma (ensures sigma i j e = 0)

val sigma_1_n_of_nats_is_nat 
  (n': nat{n' > 0}) (n: nat{0 < n /\ n <= n'}) 
  (e: (interval 1 (n' + 1)) -> nat) :
  Lemma (ensures sigma #1 #n' 1 n e >= 0)

val sigma_const_dist #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j >= i})
  (e: interval x (y + 1) -> int) (c: int) :
  Lemma (ensures sigma i j (fun i -> c * (e i)) = c * (sigma i j e))

val sigma_dist_plus #x #y 
  (i: interval x (y + 1)) (j: interval x (y+1){j >= i})
  (a: interval x (y + 1) -> int) (b: interval x (y + 1) -> int):
   Lemma (ensures sigma i j (fun i -> (a i) + (b i)) =
                  sigma i j a + sigma i j b)

val sigma_single #x #y 
  (i: interval x (y+1)) (e: interval x (y + 1) -> int)
  : 
  Lemma (sigma i i e = e i)

val sigma_split #x #y 
     
  (i: interval x (y+1)) (j: interval x (y+1){j > i})
  (k: interval x (y+1){i <= k /\ k < j})
     (e: interval x (y + 1) -> int): 
  Lemma (ensures sigma i j e = sigma i k e + sigma (k + 1) j e)

val sigma_split_end   #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i})
  (e: int -> int): 
  Lemma (sigma i j e = sigma i (j - 1) e + e j)

val sigma_split_start #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i})
  (e: interval x (y + 1) -> int):
  Lemma (ensures sigma i j e = e i + sigma (i + 1) j  e)

val sigma_split_interior #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i + 1})
  (k: interval x (y+1){i < k /\ k < j}) (e: int -> int): 
   Lemma (ensures sigma i j e = sigma i (k - 1) e + e k + sigma (k + 1) j e)

///  Any term in a sigma sum can be commuted in four cases: end to beginning, start to end, middle to beginning and end
val sigma_comm_end   #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i})
  (e: int -> int): 
  Lemma (sigma i j e = e j + sigma i (j - 1) e)

val sigma_comm_start #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i})
  (e: interval x (y + 1) -> int):
  Lemma (ensures sigma i j e = sigma (i + 1) j  e + e i)

val sigma_comm_interior_start #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i + 1})
  (k: interval x (y+1){i < k /\ k < j}) (e: int -> int): 
   Lemma (ensures sigma i j e = e k + sigma i (k - 1) e + sigma (k + 1) j e)

val sigma_comm_interior_end #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i + 1})
  (k: interval x (y+1){i < k /\ k < j}) (e: int -> int): 
   Lemma (ensures sigma i j e = sigma i (k - 1) e + sigma (k + 1) j e + e k)

///   A product from i to j of e destructing on the right.
let rec pi #x #y 
  (i: interval x (y+1)) (j: interval x (y+1))
  (e: interval x (y + 1) -> int) :
  Tot int
  (decreases j - i)
=
 if j < i
 then 1
 else if i = j
 then e j
 else pi i (j - 1) e * e j

val pi_no_range_is_one #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){i > j})
  (e: interval x (y + 1) -> int):
   Lemma (ensures pi i j e = 1)

val pi_const_exp (n: nat) (j: interval 1 (n+1)) (c: int) :
   Lemma (ensures (pi 1 j (fun i -> c)) = powx c j)

val pi_const_one #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){i <= j})
  :
   Lemma (ensures pi i j (fun i -> 1) = 1)
      
val pi_dist_times #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){i <= j})
  (a: int -> int) (b: int -> int):
   Lemma (ensures pi i j (fun i -> (a i) * (b i)) =
                  pi i j a * pi i j b)

val pi_split #x #y 
     
  (i: interval x (y+1)) (j: interval x (y+1){j > i})
  (k: interval x (y+1){i <= k /\ k < j})
     (e: int -> int): 
  Lemma (ensures pi i j e = pi i k e * pi (k + 1) j e)

val pi_split_end   #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i})
  (e: int -> int): 
  Lemma (pi i j e = pi i (j - 1) e * e j)

val pi_split_start #x (#y: int{y > x}) 
  (i: interval x (y+1)) (j: interval x (y+1){j > i})
  (e: interval x (y + 1) -> int):
  Lemma (ensures pi i j e = e i * pi (i + 1) j  e)

val pi_split_interior #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i + 1})
  (k: interval x (y+1){i < k /\ k < j}) (e: int -> int): 
   Lemma (ensures pi i j e = pi i (k - 1) e * e k * pi (k + 1) j e)

///  Any term in a pi sum can be commuted in four cases: end to beginning, start to end, middle to beginning and end
val pi_comm_end   #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i})
  (e: int -> int): 
  Lemma (pi i j e = e j * pi i (j - 1) e)

val pi_comm_start #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i})
  (e: interval x (y + 1) -> int):
  Lemma (ensures pi i j e = pi (i + 1) j  e * e i)

val pi_comm_interior_start #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i + 1}) (k: interval x (y+1){i < k /\ k < j}) 
  (e: int -> int): 
   Lemma (ensures pi i j e = e k * pi i (k - 1) e * pi (k + 1) j e)

val pi_comm_interior_end #x #y 
  (i: interval x (y+1)) (j: interval x (y+1){j > i + 1}) (k: interval x (y+1){i < k /\ k < j}) 
  (e: int -> int): 
   Lemma (ensures pi i j e = pi i (k - 1) e * pi (k + 1) j e * e k)
