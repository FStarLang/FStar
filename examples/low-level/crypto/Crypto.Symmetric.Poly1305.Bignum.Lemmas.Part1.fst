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
module Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1

open FStar.Mul
open FStar.Ghost
(** Machine integers *)
open FStar.UInt64
(** Effects and memory layout *)
open FStar.HyperStack
(** Buffers *)
open FStar.Buffer
(** Mathematical definitions *)
open FStar.Math.Lib
open FStar.Math.Lemmas

open Crypto.Symmetric.Poly1305.Parameters
open Crypto.Symmetric.Poly1305.Bigint

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack

val prime: p:erased pos{reveal p = Crypto.Symmetric.Poly1305.Spec.p_1305}
let prime = hide (Crypto.Symmetric.Poly1305.Spec.p_1305)

let willNotOverflow (h:heap) (a:bigint) (b:bigint) : GTot Type0 =
  live h a /\ live h b /\ length a >= norm_length /\ length b >= norm_length
  /\ v (get h a 0) + v (get h b 0) < pow2 64
  /\ v (get h a 1) + v (get h b 1) < pow2 64
  /\ v (get h a 2) + v (get h b 2) < pow2 64
  /\ v (get h a 3) + v (get h b 3) < pow2 64
  /\ v (get h a 4) + v (get h b 4) < pow2 64

let isSum (h:heap) (h1:heap) (a:bigint) (b:bigint) : GTot Type0 =
  live h a /\ live h1 a /\ live h b /\ length a >= norm_length /\ length b >= norm_length
  /\ v (get h a 0) + v (get h b 0) = v (get h1 a 0)
  /\ v (get h a 1) + v (get h b 1) = v (get h1 a 1)
  /\ v (get h a 2) + v (get h b 2) = v (get h1 a 2)
  /\ v (get h a 3) + v (get h b 3) = v (get h1 a 3)
  /\ v (get h a 4) + v (get h b 4) = v (get h1 a 4)

let bound27 (h:heap) (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length
  /\ v (get h b 0) < pow2 27
  /\ v (get h b 1) < pow2 27
  /\ v (get h b 2) < pow2 27
  /\ v (get h b 3) < pow2 27
  /\ v (get h b 4) < pow2 27

let w : U32.t -> Tot int = U32.v


(*** Addition ***)

#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_fsum_0:
  a0:U64.t -> a1:U64.t -> a2:U64.t -> a3:U64.t -> a4:U64.t ->
  b0:U64.t -> b1:U64.t -> b2:U64.t -> b3:U64.t -> b4:U64.t ->
  Lemma (requires (let open FStar.UInt64 in
	  v a0 < pow2 26 /\ v a1 < pow2 26 /\ v a2 < pow2 26 /\ v a3 < pow2 26 /\ v a4 < pow2 26
	  /\ v b0 < pow2 26 /\ v b1 < pow2 26 /\ v b2 < pow2 26 /\ v b3 < pow2 26 /\ v b4 < pow2 26))
	(ensures  (let open FStar.UInt64 in
		  v a0 + v b0 < pow2 64 /\ v a1 + v b1 < pow2 64 /\ v a2 + v b2 < pow2 64
		  /\ v a3 + v b3 < pow2 64 /\ v a4 + v b4 < pow2 64))
let lemma_fsum_0 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =
  pow2_double_sum 26;
  pow2_lt_compat 64 27

#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_bitweight_values: unit ->
  Lemma (bitweight templ 0 = 0 /\ bitweight templ 1 = 26
	/\ bitweight templ 2 = 52 /\ bitweight templ 3 = 78
	/\ bitweight templ 4 = 104 /\ bitweight templ 5 = 130
	/\ bitweight templ 6 = 156 /\ bitweight templ 7 = 182
	/\ bitweight templ 8 = 208 /\ bitweight templ 9 = 234)
let lemma_bitweight_values () =
  bitweight_def templ 0;
  bitweight_def templ 1;
  bitweight_def templ 2;
  bitweight_def templ 3;
  bitweight_def templ 4;
  bitweight_def templ 5;
  bitweight_def templ 6;
  bitweight_def templ 7;
  bitweight_def templ 8;
  bitweight_def templ 9

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_eval_bigint_5:
  h:mem ->
  b:bigint ->
  Lemma (requires (live h b))
	(ensures  (live h b
	  /\ eval h b norm_length = v (get h b 0) + pow2 26  * v (get h b 1)
						  + pow2 52  * v (get h b 2)
						  + pow2 78  * v (get h b 3)
						  + pow2 104 * v (get h b 4) ))
let lemma_eval_bigint_5 h b =
  lemma_bitweight_values ();
  eval_def h b 0;
  eval_def h b 1;
  eval_def h b 2;
  eval_def h b 3;
  eval_def h b 4;
  eval_def h b 5

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_eval_bigint_6:
  h:mem ->
  b:bigint ->
  Lemma (requires (live h b /\ length b >= norm_length+1))
	(ensures  (live h b /\ length b >= norm_length+1
	  /\ eval h b (norm_length+1) = v (get h b 0) + pow2 26  * v (get h b 1)
						     + pow2 52  * v (get h b 2)
						     + pow2 78  * v (get h b 3)
						     + pow2 104 * v (get h b 4)
						     + pow2 130 * v (get h b 5) ))
let lemma_eval_bigint_6 h b =
  lemma_bitweight_values ();
  eval_def h b 0;
  eval_def h b 1;
  eval_def h b 2;
  eval_def h b 3;
  eval_def h b 4;
  eval_def h b 5;
  eval_def h b 6

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_eval_bigint_9:
  h:mem ->
  b:bigint ->
  Lemma (requires (live h b /\ length b >= 2*norm_length-1))
	(ensures  (live h b /\ length b >= 2*norm_length-1
	  /\ eval h b (2*norm_length-1) = v (get h b 0) + pow2 26  * v (get h b 1)
						       + pow2 52  * v (get h b 2)
						       + pow2 78  * v (get h b 3)
						       + pow2 104 * v (get h b 4)
						       + pow2 130 * v (get h b 5)
						       + pow2 156 * v (get h b 6)
						       + pow2 182 * v (get h b 7)
						       + pow2 208 * v (get h b 8) ))
let lemma_eval_bigint_9 h b =
  lemma_bitweight_values ();
  eval_def h b 0;
  eval_def h b 1;
  eval_def h b 2;
  eval_def h b 3;
  eval_def h b 4;
  eval_def h b 5;
  eval_def h b 6;
  eval_def h b 7;
  eval_def h b 8;
  eval_def h b 9

#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val factorization_lemma: unit ->
  Lemma (requires (True))
	(ensures  (forall a b c. {:pattern (a * (b+c))} a * (b + c) = a * b + a * c))
let factorization_lemma () = ()

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_fsum: h0:mem -> h1:mem -> a:bigint -> b:bigint -> Lemma
  (requires (norm h0 a /\ norm h0 b /\ isSum h0 h1 a b))
  (ensures  (norm h0 a /\ norm h0 b /\ isSum h0 h1 a b
    /\ bound27 h1 a /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length))
let lemma_fsum h0 h1 a b =
  pow2_double_sum 26;
  lemma_eval_bigint_5 h0 a;
  lemma_eval_bigint_5 h0 b;
  factorization_lemma ();
  lemma_eval_bigint_5 h1 a

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

let isMultiplication (h0:mem) (h1:mem) (a:bigint) (b:bigint) (c:bigint) : GTot Type0 =
  live h0 a /\ live h0 b /\ live h1 c
  /\ length a >= norm_length /\ length b >= norm_length /\ length c >= 2*norm_length-1
  /\ (
    let a0 = v (get h0 a 0) in let a1 = v (get h0 a 1) in let a2 = v (get h0 a 2) in
    let a3 = v (get h0 a 3) in let a4 = v (get h0 a 4) in let b0 = v (get h0 b 0) in
    let b1 = v (get h0 b 1) in let b2 = v (get h0 b 2) in let b3 = v (get h0 b 3) in
    let b4 = v (get h0 b 4) in let c0 = v (get h1 c 0) in let c1 = v (get h1 c 1) in
    let c2 = v (get h1 c 2) in let c3 = v (get h1 c 3) in let c4 = v (get h1 c 4) in
    let c5 = v (get h1 c 5) in let c6 = v (get h1 c 6) in let c7 = v (get h1 c 7) in
    let c8 = v (get h1 c 8) in
    ( c0 = a0 * b0
      /\ c1 = a0 * b1 + a1 * b0
      /\ c2 = a0 * b2 + a1 * b1 + a2 * b0
      /\ c3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
      /\ c4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0
      /\ c5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1
      /\ c6 = a2 * b4 + a3 * b3 + a4 * b2
      /\ c7 = a3 * b4 + a4 * b3
      /\ c8 = a4 * b4 ) )

let isMultiplication_
  (h1:mem)
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int)
  (c:bigint) : GTot Type0 =
  live h1 c /\ length c >= 2*norm_length-1
  /\ (
      let c0 = v (get h1 c 0) in let c1 = v (get h1 c 1) in
      let c2 = v (get h1 c 2) in let c3 = v (get h1 c 3) in let c4 = v (get h1 c 4) in
      let c5 = v (get h1 c 5) in let c6 = v (get h1 c 6) in let c7 = v (get h1 c 7) in
      let c8 = v (get h1 c 8) in
      ( c0 = a0 * b0
	/\ c1 = a0 * b1 + a1 * b0
	/\ c2 = a0 * b2 + a1 * b1 + a2 * b0
	/\ c3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
	/\ c4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0
	/\ c5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1
	/\ c6 = a2 * b4 + a3 * b3 + a4 * b2
	/\ c7 = a3 * b4 + a4 * b3
	/\ c8 = a4 * b4 ) )

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_multiplication_0:
  a0:U64.t -> a1:U64.t -> a2:U64.t -> a3:U64.t -> a4:U64.t ->
  b0:U64.t -> b1:U64.t -> b2:U64.t -> b3:U64.t -> b4:U64.t ->
  Lemma (requires (let open FStar.UInt64 in
	  v a0 < pow2 27 /\ v a1 < pow2 27 /\ v a2 < pow2 27 /\ v a3 < pow2 27 /\ v a4 < pow2 27
	  /\ v b0 < pow2 26 /\ v b1 < pow2 26 /\ v b2 < pow2 26 /\ v b3 < pow2 26 /\ v b4 < pow2 26))
	(ensures  (let open FStar.UInt64 in
	  v a0 * v b0 < pow2 64 /\ v a1 * v b0 < pow2 64 /\ v a2 * v b0 < pow2 64
	  /\ v a3 * v b0 < pow2 64 /\ v a4 * v b0 < pow2 64 /\ v a0 * v b1 < pow2 64
	  /\ v a1 * v b1 < pow2 64 /\ v a2 * v b1 < pow2 64 /\ v a3 * v b1 < pow2 64
	  /\ v a4 * v b1 < pow2 64 /\ v a0 * v b2 < pow2 64 /\ v a1 * v b2 < pow2 64
	  /\ v a2 * v b2 < pow2 64 /\ v a3 * v b2 < pow2 64 /\ v a4 * v b2 < pow2 64
	  /\ v a0 * v b3 < pow2 64 /\ v a1 * v b3 < pow2 64 /\ v a2 * v b3 < pow2 64
	  /\ v a3 * v b3 < pow2 64 /\ v a4 * v b3 < pow2 64 /\ v a0 * v b4 < pow2 64
	  /\ v a1 * v b4 < pow2 64 /\ v a2 * v b4 < pow2 64 /\ v a3 * v b4 < pow2 64
	  /\ v a4 * v b4 < pow2 64
	  /\ v a0 * v b1 + v a1 * v b0 < pow2 64
	  /\ v a0 * v b2 + v a1 * v b1 < pow2 64
	  /\ v a0 * v b2 + v a1 * v b1 + v a2 * v b0 < pow2 64
	  /\ v a0 * v b3 + v a1 * v b2 < pow2 64
	  /\ v a0 * v b3 + v a1 * v b2 + v a2 * v b1 < pow2 64
	  /\ v a0 * v b3 + v a1 * v b2 + v a2 * v b1 + v a3 * v b0 < pow2 64
	  /\ v a0 * v b4 + v a1 * v b3 < pow2 64
	  /\ v a0 * v b4 + v a1 * v b3 + v a2 * v b2 < pow2 64
	  /\ v a0 * v b4 + v a1 * v b3 + v a2 * v b2 + v a3 * v b1 < pow2 64
	  /\ v a0 * v b4 + v a1 * v b3 + v a2 * v b2 + v a3 * v b1 + v a4 * v b0 < pow2 64
	  /\ v a1 * v b4 + v a2 * v b3 < pow2 64
	  /\ v a1 * v b4 + v a2 * v b3 + v a3 * v b2 < pow2 64
	  /\ v a1 * v b4 + v a2 * v b3 + v a3 * v b2 + v a4 * v b1 < pow2 64
	  /\ v a2 * v b4 + v a3 * v b3 < pow2 64
	  /\ v a2 * v b4 + v a3 * v b3 + v a4 * v b2 < pow2 64
	  /\ v a3 * v b4 + v a4 * v b3 < pow2 64
	  ))
let lemma_multiplication_0 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =
  assert(forall (a:nat) (b:nat) c d. {:pattern (a * b); (c * d)} (a < c /\ b < d) ==> a * b < c * d);
  pow2_plus 27 26;
  pow2_lt_compat 64 53;
  pow2_double_sum 53;
  pow2_lt_compat 64 54;
  pow2_double_sum 54;
  pow2_lt_compat 64 55;
  pow2_double_sum 55;
  pow2_lt_compat 64 56

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

let u27 = x:FStar.UInt64.t{v x < pow2 27}
let u26 = x:FStar.UInt64.t{v x < pow2 26}


let lemma_multiplication00 a b c :
  Lemma (a * (b + c) = a * b + a * c)
  = ()
let lemma_multiplication01 a b c d:
  Lemma (a * (b + c + d) = a * b + a * c + a * d)
  = ()
let lemma_multiplication02 a b c d e :
  Lemma (a * (b + c + d + e) = a * b + a * c + a * d + a * e)
  = ()
let lemma_multiplication03 a b c d e f :
  Lemma (a * (b + c + d + e + f) = a * b + a * c + a * d + a * e + a * f)
  = ()
private let lemma_multiplication03bis a b c d e f :
  Lemma ((b + c + d + e + f) * a = b * a + c * a + d * a + e * a + f * a)
  = ()
private let lemma_multiplication04 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 :
  Lemma ((a0+a1+a2+a3+a4)*(b0+b1+b2+b3+b4)
    = a0*b0+a0*b1+a0*b2+a0*b3+a0*b4
      +a1*b0+a1*b1+a1*b2+a1*b3+a1*b4
      +a2*b0+a2*b1+a2*b2+a2*b3+a2*b4
      +a3*b0+a3*b1+a3*b2+a3*b3+a3*b4
      +a4*b0+a4*b1+a4*b2+a4*b3+a4*b4)
  = lemma_multiplication03bis (b0+b1+b2+b3+b4) a0 a1 a2 a3 a4;
    lemma_multiplication03 a0 b0 b1 b2 b3 b4;
    lemma_multiplication03 a1 b0 b1 b2 b3 b4;
    lemma_multiplication03 a2 b0 b1 b2 b3 b4;
    lemma_multiplication03 a3 b0 b1 b2 b3 b4;
    lemma_multiplication03 a4 b0 b1 b2 b3 b4

#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let lemma_multiplication05
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma ((a0 + pow2 26 * a1 + pow2 52 * a2 + pow2 78 * a3 + pow2 104 * a4)
    * (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4)
    = a0*b0+a0*(pow2 26*b1)+a0*(pow2 52*b2)+a0*(pow2 78*b3)+a0*(pow2 104*b4)
      +(pow2 26*a1)*b0+(pow2 26*a1)*(pow2 26*b1)+(pow2 26*a1)*(pow2 52*b2)+(pow2 26*a1)*(pow2 78*b3)+(pow2 26*a1)*(pow2 104*b4)
      +(pow2 52*a2)*b0+(pow2 52*a2)*(pow2 26*b1)+(pow2 52*a2)*(pow2 52*b2)+(pow2 52*a2)*(pow2 78*b3)+(pow2 52*a2)*(pow2 104*b4)
      +(pow2 78*a3)*b0+(pow2 78*a3)*(pow2 26*b1)+(pow2 78*a3)*(pow2 52*b2)+(pow2 78*a3)*(pow2 78*b3)+(pow2 78*a3)*(pow2 104*b4)
      +(pow2 104*a4)*b0+(pow2 104*a4)*(pow2 26*b1)+(pow2 104*a4)*(pow2 52*b2) +(pow2 104*a4)*(pow2 78*b3)+(pow2 104*a4)*(pow2 104*b4) )
  = lemma_multiplication04 (a0) (pow2 26 * a1) (pow2 52 * a2) (pow2 78 * a3) (pow2 104 * a4)
			   (b0) (pow2 26 * b1) (pow2 52 * b2) (pow2 78 * b3) (pow2 104 * b4)


(*
#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication060
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    a0*b0+a0*(pow2 26*b1)+a0*(pow2 52*b2)+a0*(pow2 78*b3)+a0*(pow2 104*b4)
    = a0 * b0 + pow2 26  * (a0 * b1) + pow2 52  * (a0 * b2) + pow2 78  * (a0 * b3) + pow2 104 * (a0 * b4) )
  = ()

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

let lemma_swap p1 a p2 b : Lemma ((p1 * a) * (p2 * b) = p1 * p2 * (a * b)) = ()

private let lemma_multiplication061
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    (pow2 26*a1)*b0+(pow2 26*a1)*(pow2 26*b1)+(pow2 26*a1)*(pow2 52*b2)+(pow2 26*a1)*(pow2 78*b3)+(pow2 26*a1)*(pow2 104*b4)
    = pow2 26 * (a1 * b0) + pow2 52 * (a1 * b1) + pow2 78 * (a1 * b2) + pow2 104 * (a1 * b3) + pow2 130 * (a1 * b4) )
  = pow2_plus 26 26;
    pow2_plus 26 52;
    pow2_plus 26 78;
    pow2_plus 26 104;
    lemma_swap (pow2 26) a1 (pow2 26) b1;
    lemma_swap (pow2 26) a1 (pow2 52) b2;
    lemma_swap (pow2 26) a1 (pow2 78) b3;
    lemma_swap (pow2 26) a1 (pow2 104) b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication062
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    (pow2 52*a2)*b0+(pow2 52*a2)*(pow2 26*b1)+(pow2 52*a2)*(pow2 52*b2)+(pow2 52*a2)*(pow2 78*b3)+(pow2 52*a2)*(pow2 104*b4)
    = pow2 52  * (a2 * b0) + pow2 78  * (a2 * b1) + pow2 104 * (a2 * b2) + pow2 130 * (a2 * b3) + pow2 156 * (a2 * b4) )
  = pow2_plus 52 26;
    pow2_plus 52 52;
    pow2_plus 52 78;
    pow2_plus 52 104;
    lemma_swap (pow2 52) a2 (pow2 26) b1;
    lemma_swap (pow2 52) a2 (pow2 52) b2;
    lemma_swap (pow2 52) a2 (pow2 78) b3;
    lemma_swap (pow2 52) a2 (pow2 104) b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication063
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    (pow2 78*a3)*b0+(pow2 78*a3)*(pow2 26*b1)+(pow2 78*a3)*(pow2 52*b2)+(pow2 78*a3)*(pow2 78*b3)+(pow2 78*a3)*(pow2 104*b4)
    = pow2 78  * (a3 * b0) + pow2 104 * (a3 * b1) + pow2 130 * (a3 * b2) + pow2 156 * (a3 * b3) + pow2 182 * (a3 * b4) )
  = pow2_plus 78 26;
    pow2_plus 78 52;
    pow2_plus 78 78;
    pow2_plus 78 104;
    lemma_swap (pow2 78) a3 (pow2 26) b1;
    lemma_swap (pow2 78) a3 (pow2 52) b2;
    lemma_swap (pow2 78) a3 (pow2 78) b3;
    lemma_swap (pow2 78) a3 (pow2 104) b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication064
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    (pow2 104*a4)*b0+(pow2 104*a4)*(pow2 26*b1)+(pow2 104*a4)*(pow2 52*b2) +(pow2 104*a4)*(pow2 78*b3)+(pow2 104*a4)*(pow2 104*b4)
    = pow2 104 * (a4 * b0) + pow2 130 * (a4 * b1) + pow2 156 * (a4 * b2) + pow2 182 * (a4 * b3) + pow2 208 * (a4 * b4) )
  = pow2_plus 104 26;
    pow2_plus 104 52;
    pow2_plus 104 78;
    pow2_plus 104 104;
    lemma_swap (pow2 104) a4 (pow2 26) b1;
    lemma_swap (pow2 104) a4 (pow2 52) b2;
    lemma_swap (pow2 104) a4 (pow2 78) b3;
    lemma_swap (pow2 104) a4 (pow2 104) b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication06
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    a0*b0+a0*(pow2 26*b1)+a0*(pow2 52*b2)+a0*(pow2 78*b3)+a0*(pow2 104*b4)
      +(pow2 26*a1)*b0+(pow2 26*a1)*(pow2 26*b1)+(pow2 26*a1)*(pow2 52*b2)+(pow2 26*a1)*(pow2 78*b3)+(pow2 26*a1)*(pow2 104*b4)
      +(pow2 52*a2)*b0+(pow2 52*a2)*(pow2 26*b1)+(pow2 52*a2)*(pow2 52*b2)+(pow2 52*a2)*(pow2 78*b3)+(pow2 52*a2)*(pow2 104*b4)
      +(pow2 78*a3)*b0+(pow2 78*a3)*(pow2 26*b1)+(pow2 78*a3)*(pow2 52*b2)+(pow2 78*a3)*(pow2 78*b3)+(pow2 78*a3)*(pow2 104*b4)
      +(pow2 104*a4)*b0+(pow2 104*a4)*(pow2 26*b1)+(pow2 104*a4)*(pow2 52*b2) +(pow2 104*a4)*(pow2 78*b3)+(pow2 104*a4)*(pow2 104*b4)
    =              (a0 * b0) + pow2 26  * (a0 * b1) + pow2 52  * (a0 * b2) + pow2 78  * (a0 * b3) + pow2 104 * (a0 * b4)
      + pow2 26  * (a1 * b0) + pow2 52  * (a1 * b1) + pow2 78  * (a1 * b2) + pow2 104 * (a1 * b3) + pow2 130 * (a1 * b4)
      + pow2 52  * (a2 * b0) + pow2 78  * (a2 * b1) + pow2 104 * (a2 * b2) + pow2 130 * (a2 * b3) + pow2 156 * (a2 * b4)
      + pow2 78  * (a3 * b0) + pow2 104 * (a3 * b1) + pow2 130 * (a3 * b2) + pow2 156 * (a3 * b3) + pow2 182 * (a3 * b4)
      + pow2 104 * (a4 * b0) + pow2 130 * (a4 * b1) + pow2 156 * (a4 * b2) + pow2 182 * (a4 * b3) + pow2 208 * (a4 * b4) )
  = lemma_multiplication060 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication061 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication062 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication063 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication064 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication07
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma ((a0 + pow2 26 * a1 + pow2 52 * a2 + pow2 78 * a3 + pow2 104 * a4)
    * (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4)
    =              (a0 * b0) + pow2 26  * (a0 * b1) + pow2 52  * (a0 * b2) + pow2 78  * (a0 * b3) + pow2 104 * (a0 * b4)
      + pow2 26  * (a1 * b0) + pow2 52  * (a1 * b1) + pow2 78  * (a1 * b2) + pow2 104 * (a1 * b3) + pow2 130 * (a1 * b4)
      + pow2 52  * (a2 * b0) + pow2 78  * (a2 * b1) + pow2 104 * (a2 * b2) + pow2 130 * (a2 * b3) + pow2 156 * (a2 * b4)
      + pow2 78  * (a3 * b0) + pow2 104 * (a3 * b1) + pow2 130 * (a3 * b2) + pow2 156 * (a3 * b3) + pow2 182 * (a3 * b4)
      + pow2 104 * (a4 * b0) + pow2 130 * (a4 * b1) + pow2 156 * (a4 * b2) + pow2 182 * (a4 * b3) + pow2 208 * (a4 * b4) )
  = lemma_multiplication05 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication06 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication08
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    a0 * b0 + pow2 26  * (a1 * b0 + a0 * b1)
	    + pow2 52  * (a2 * b0 + a1 * b1 + a0 * b2)
	    + pow2 78  * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3)
	    + pow2 104 * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4)
	    + pow2 130 * (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4)
	    + pow2 156 * (a4 * b2 + a3 * b3 + a2 * b4)
	    + pow2 182 * (a4 * b3 + a3 * b4)
	    + pow2 208 * (a4 * b4)
    =              (a0 * b0) + pow2 26  * (a0 * b1) + pow2 52  * (a0 * b2) + pow2 78  * (a0 * b3) + pow2 104 * (a0 * b4)
      + pow2 26  * (a1 * b0) + pow2 52  * (a1 * b1) + pow2 78  * (a1 * b2) + pow2 104 * (a1 * b3) + pow2 130 * (a1 * b4)
      + pow2 52  * (a2 * b0) + pow2 78  * (a2 * b1) + pow2 104 * (a2 * b2) + pow2 130 * (a2 * b3) + pow2 156 * (a2 * b4)
      + pow2 78  * (a3 * b0) + pow2 104 * (a3 * b1) + pow2 130 * (a3 * b2) + pow2 156 * (a3 * b3) + pow2 182 * (a3 * b4)
      + pow2 104 * (a4 * b0) + pow2 130 * (a4 * b1) + pow2 156 * (a4 * b2) + pow2 182 * (a4 * b3) + pow2 208 * (a4 * b4) )
  = lemma_multiplication00 (pow2 26) (a1 * b0) (a0 * b1);
    lemma_multiplication01 (pow2 52) (a2 * b0) (a1 * b1) (a0 * b2);
    lemma_multiplication02 (pow2 78) (a3 * b0) (a2 * b1) (a1 * b2) (a0 * b3);
    lemma_multiplication03 (pow2 104) (a4 * b0) (a3 * b1) (a2 * b2) (a1 * b3) (a0 * b4);
    lemma_multiplication02 (pow2 130) (a4 * b1) (a3 * b2) (a2 * b3) (a1 * b4);
    lemma_multiplication01 (pow2 156) (a4 * b2) (a3 * b3) (a2 * b4);
    lemma_multiplication00 (pow2 182) (a4 * b3) (a3 * b4)


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication0
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    (a0 + pow2 26 * a1 + pow2 52 * a2 + pow2 78 * a3 + pow2 104 * a4)
    * (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4) =
    a0 * b0 + pow2 26  * (a1 * b0 + a0 * b1)
	    + pow2 52  * (a2 * b0 + a1 * b1 + a0 * b2)
	    + pow2 78  * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3)
	    + pow2 104 * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4)
	    + pow2 130 * (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4)
	    + pow2 156 * (a4 * b2 + a3 * b3 + a2 * b4)
	    + pow2 182 * (a4 * b3 + a3 * b4)
	    + pow2 208 * (a4 * b4) )
  = lemma_multiplication07 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication08 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_multiplication1:
  h0:mem -> h1:mem ->
  c:bigint{length c >= 2*norm_length-1} ->
  a:bigint -> b:bigint ->
  Lemma (requires (isMultiplication h0 h1 a b c))
	(ensures  (isMultiplication h0 h1 a b c
	  /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * eval h0 b norm_length))
let lemma_multiplication1 h0 h1 c a b =
  let a0 = v (get h0 a 0) in
  let a1 = v (get h0 a 1) in
  let a2 = v (get h0 a 2) in
  let a3 = v (get h0 a 3) in
  let a4 = v (get h0 a 4) in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  lemma_eval_bigint_9 h1 c;
  lemma_eval_bigint_5 h0 a;
  lemma_eval_bigint_5 h0 b;
  lemma_multiplication0 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4


#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

let lemma_mul_ineq (a:nat) (b:nat) c d : Lemma (requires (a < c /\ b < d))
					    (ensures  (a * b < c * d))
  = ()

val lemma_multiplication2:
  h0:mem -> h1:mem ->
  c:bigint{length c >= 2*norm_length-1} ->
  a:bigint -> b:bigint ->
  Lemma (requires (bound27 h0 a /\ norm h0 b /\ isMultiplication h0 h1 a b c))
	(ensures  (bound27 h0 a /\ norm h0 b /\ isMultiplication h0 h1 a b c
	  /\ maxValue h1 c 9 <= norm_length * pow2 53))
let lemma_multiplication2 h0 h1 c a b =
  pow2_plus 27 26;
  let a0 = v (get h0 a 0) in
  let a1 = v (get h0 a 1) in
  let a2 = v (get h0 a 2) in
  let a3 = v (get h0 a 3) in
  let a4 = v (get h0 a 4) in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  lemma_mul_ineq a0 b0 (pow2 27) (pow2 26);
  lemma_mul_ineq a0 b1 (pow2 27) (pow2 26);
  lemma_mul_ineq a0 b2 (pow2 27) (pow2 26);
  lemma_mul_ineq a0 b3 (pow2 27) (pow2 26);
  lemma_mul_ineq a0 b4 (pow2 27) (pow2 26);
  lemma_mul_ineq a1 b0 (pow2 27) (pow2 26);
  lemma_mul_ineq a1 b1 (pow2 27) (pow2 26);
  lemma_mul_ineq a1 b2 (pow2 27) (pow2 26);
  lemma_mul_ineq a1 b3 (pow2 27) (pow2 26);
  lemma_mul_ineq a1 b4 (pow2 27) (pow2 26);
  lemma_mul_ineq a2 b0 (pow2 27) (pow2 26);
  lemma_mul_ineq a2 b1 (pow2 27) (pow2 26);
  lemma_mul_ineq a2 b2 (pow2 27) (pow2 26);
  lemma_mul_ineq a2 b3 (pow2 27) (pow2 26);
  lemma_mul_ineq a2 b4 (pow2 27) (pow2 26);
  lemma_mul_ineq a3 b0 (pow2 27) (pow2 26);
  lemma_mul_ineq a3 b1 (pow2 27) (pow2 26);
  lemma_mul_ineq a3 b2 (pow2 27) (pow2 26);
  lemma_mul_ineq a3 b3 (pow2 27) (pow2 26);
  lemma_mul_ineq a3 b4 (pow2 27) (pow2 26);
  lemma_mul_ineq a4 b0 (pow2 27) (pow2 26);
  lemma_mul_ineq a4 b1 (pow2 27) (pow2 26);
  lemma_mul_ineq a4 b2 (pow2 27) (pow2 26);
  lemma_mul_ineq a4 b3 (pow2 27) (pow2 26);
  lemma_mul_ineq a4 b4 (pow2 27) (pow2 26);
  assert(v (get h1 c 0) < pow2 53);
  assert(v (get h1 c 1) < 2*pow2 53);
  assert(v (get h1 c 2) < 3*pow2 53);
  assert(v (get h1 c 3) < 4*pow2 53);
  assert(v (get h1 c 4) < 5*pow2 53);
  assert(v (get h1 c 5) < 4*pow2 53);
  assert(v (get h1 c 6) < 3*pow2 53);
  assert(v (get h1 c 7) < 2*pow2 53);
  assert(v (get h1 c 8) < pow2 53);
  maxValue_bound_lemma_aux h1 c (2*norm_length-1) (5*pow2 53)


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_multiplication:
  h0:mem ->
  h1:mem ->
  c:bigint{length c >= 2*norm_length-1} ->
  a:bigint{disjoint c a} ->
  b:bigint{disjoint c b} ->
  Lemma (requires (bound27 h0 a /\ norm h0 b /\ live h1 c /\ isMultiplication h0 h1 a b c))
	(ensures  (bound27 h0 a /\ norm h0 b /\ live h1 c /\ isMultiplication h0 h1 a b c
	  /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * eval h0 b norm_length
	  /\ maxValue h1 c (2*norm_length-1) <= norm_length * pow2 53))
let lemma_multiplication h0 h1 c a b =
  lemma_multiplication1 h0 h1 c a b;
  lemma_multiplication2 h0 h1 c a b
