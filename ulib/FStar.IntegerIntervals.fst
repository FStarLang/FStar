(*
   Copyright 2008-2022 Microsoft Research
   
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
   
       http://www.apache.org/licenses/LICENSE-2.0
       
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: A. Rozanov
*)
module FStar.IntegerIntervals
 
(* Aliases to all kinds of integer intervals *)

(* general infinite integer intervals *)
type less_than (k: int) = x:int{x<k}
type greater_than (k: int) = x:int{x>k}
type not_less_than (x: int) = greater_than (x-1)
type not_greater_than (x: int) = less_than (x+1)

(* Type coercion. While supposed to be absolutely trivial, 
   might still be invoked directly under extremely low rlimits *)
let coerce_to_less_than #n (x: not_greater_than n) : less_than (n+1) = x
let coerce_to_not_less_than #n (x: greater_than n) : not_less_than (n+1) = x

let interval_condition (x y t: int) = (x <= t) && (t < y)

type interval_type (x y:int) = z : Type0{ z == t:int{interval_condition x y t} }

(* Default interval is half-open, which is the most frequently used case *) 
type interval (x y: int) : interval_type x y = t:int{interval_condition x y t}

(* general finite integer intervals *)
type efrom_eto (x y: int) = interval (x+1) y
type efrom_ito (x y: int) = interval (x+1) (y+1)
type ifrom_eto (x y: int) = interval x y
type ifrom_ito (x y: int) = interval x (y+1)

(* Special case for naturals under k, to use in sequences, lists, arrays, etc *)
type under (k: nat) = interval 0 k

(* If we define our intervals this way, then the following lemma comes for free: *)
private let closed_interval_lemma (x y:int) : Lemma (interval x (y+1) == ifrom_ito x y) = ()


(* how many numbers fall into an interval? *)
let interval_size (#x #y: int) (interval: interval_type x y) : nat 
  = if y >= x then y-x else 0

(* when we want a zero-based index that runs over an interval, we use this *)
type counter_for (#x #y:int) (interval: interval_type x y) = under (interval_size interval)

(* special case for closed intervals, used in FStar.Algebra.CommMonoid.Fold *)
let closed_interval_size (x y: int) : nat = interval_size (ifrom_ito x y)

(* A usage example and a test at the same time: *)
private let _ = assert (interval_size (interval 5 10) = 5)
private let _ = assert (interval_size (ifrom_ito 5 10) = 6)
private let _ = assert (interval_size (ifrom_ito 15 10) = 0)

(* This lemma, especially when used with forall_intro, helps the 
   prover verify the index ranges of sequences that correspond 
   to arbitrary folds. 

   It is supposed to be invoked to decrease the toll we put on rlimit,
   i.e. will be redundant in most use cases. *)
let counter_bounds_lemma (x y:int) (i: (counter_for (ifrom_ito x y))) 
  : Lemma (x+i >= x /\ x+i <= y) = ()

(* An integer sequence [0..n), n values in total,
   with index value available to the prover. *)
let indices_seq (n: nat) 
  : (f:FStar.Seq.Base.seq (under n) {
       FStar.Seq.Base.length f = n /\ 
       (forall (k: under n). FStar.Seq.Base.index f k = k) 
    }) 
  = FStar.Seq.Base.init n (fun (x:under n) -> x)
