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
module FStar.BV
open FStar.UInt // for now just opening this for logand, logxor, etc. but we need a better solution.
 
val bv_t: (n : nat) -> t:Type0{hasEq t}

(* Redefining basic type from UInt to avoid importing UInt *)
(* Reduces verification time by 50% in small examples *)
// let max_int (n:nat) : Tot int = pow2 n - 1
// let min_int (n:nat) : Tot int = 0
// let fits (x:int) (n:nat) : Tot bool = min_int n <= x && x <= max_int n
// let size (x:int) (n:nat) : Tot Type0 = b2t(fits x n)
// type uint_t' (n:nat) = x:int{size x n}

val bv_uext: #n:pos -> #m:pos -> a:bv_t n -> Tot (normalize (bv_t (m+n)))

val bvand: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

val bvxor: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

val bvor: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

val bvnot: #n:pos -> a:bv_t n -> Tot (bv_t n)

val bvshl: #n:pos -> a:bv_t n -> s:nat -> Tot (bv_t n)

val bvshr: #n:pos -> a:bv_t n -> s:nat -> Tot (bv_t n)

val int2bv: #n:pos -> num:uint_t n -> Tot (bv_t n)

val bv2int: #n:pos -> vec:bv_t n -> Tot (uint_t n)

val list2bv: #n:pos -> l:list bool{List.length l = n} -> Tot (bv_t n)

val bv2list: #n:pos -> bv_t n -> Tot (l:list bool{List.length l = n})

unfold
let bv_zero #n = int2bv #n 0

val bvult: #n:pos -> a: bv_t n -> b: bv_t n -> Tot (bool)

val int2bv_lemma_1: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires a = b) (ensures (int2bv #n a = int2bv #n b))

val int2bv_lemma_2: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires (int2bv a = int2bv b)) (ensures a = b)

val list2bv_bij: #n:pos -> a:list bool{List.length a = n} ->
  Lemma (requires (True))
        (ensures (bv2list (list2bv #n a) = a))

val bv2list_bij: #n:pos -> a:bv_t n ->
  Lemma (requires (True))
        (ensures (list2bv (bv2list #n a) = a))

val bvadd :#n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)
val bvsub :#n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)
val bvdiv :#n:pos -> a:bv_t n -> b:uint_t n{b <> 0} -> Tot (bv_t n)
val bvmod :#n:pos -> a:bv_t n -> b:uint_t n{b <> 0} -> Tot (bv_t n)
val bvmul :#n:pos -> a:bv_t n -> b:uint_t n -> Tot (bv_t n)

val inverse_vec_lemma: #n:pos -> vec:bv_t n ->
  Lemma (requires True) (ensures vec = (int2bv (bv2int vec)))
        [SMTPat (int2bv (bv2int vec))]

val inverse_num_lemma: #n:pos -> num:uint_t n ->
  Lemma (requires True) (ensures num = bv2int #n (int2bv #n num))
        [SMTPat (bv2int #n (int2bv #n num))]

(* Lemmas connecting logical arithmetic and bitvectors *)

val int2bv_lemma_ult_1: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires a < b) (ensures (bvult #n (int2bv #n a) (int2bv #n b)))

val int2bv_lemma_ult_2: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires (bvult #n (int2bv #n a) (int2bv #n b))) (ensures a < b)

val int2bv_logand : (#n:pos) -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
			    squash (bvand #n (int2bv #n x) (int2bv #n y) == z) ->
			    Lemma (int2bv #n (logand #n x y) == z)

 val int2bv_logxor : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
		     squash (bvxor #n (int2bv #n x) (int2bv #n y) == z) ->
		     Lemma (int2bv #n (logxor #n x y) == z)

 val int2bv_logor : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
		     squash (bvor #n (int2bv #n x) (int2bv #n y) == z) ->
		     Lemma (int2bv #n (logor #n x y) == z)

 val int2bv_shl : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
			    squash (bvshl #n (int2bv #n x) y == z) ->
			    Lemma (int2bv #n (shift_left #n x y) == z)

 val int2bv_shr : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
			    squash (bvshr #n (int2bv #n x) y == z) ->
			    Lemma (int2bv #n (shift_right #n x y) == z)

val int2bv_add : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
			    squash (bvadd #n (int2bv #n x) (int2bv #n y) == z) ->
			    Lemma (int2bv #n (add_mod #n x y) == z)

val int2bv_sub : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
			    squash (bvsub #n (int2bv #n x) (int2bv #n y) == z) ->
			    Lemma (int2bv #n (sub_mod #n x y) == z)

 val int2bv_div : #n:pos -> (#x:uint_t n) -> (#y:uint_t n{y <> 0}) -> (#z:bv_t n) ->
			    squash (bvdiv #n (int2bv #n x) y == z) ->
			    Lemma (int2bv #n (udiv #n x y) == z)

 val int2bv_mod : #n:pos -> (#x:uint_t n) -> (#y:uint_t n{y <> 0}) -> (#z:bv_t n) ->
			    squash (bvmod #n (int2bv #n x) y == z) ->
			    Lemma (int2bv #n (mod #n x y) == z)
			    
 val int2bv_mul : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
			    squash (bvmul #n (int2bv #n x) y == z) ->
			    Lemma (int2bv #n (mul_mod #n x y) == z)
