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

module U = FStar.UInt
module B = FStar.BitVector
module S = FStar.Seq

let bv_t (n : nat) = B.bv_t n

let bv_uext #n #i a =
  Seq.append (Seq.create i false) a

let int2bv = U.to_vec
let bv2int = U.from_vec

let int2bv_lemma_1 = U.to_vec_lemma_1
let int2bv_lemma_2 = U.to_vec_lemma_2
let inverse_vec_lemma = U.inverse_vec_lemma
let inverse_num_lemma = U.inverse_num_lemma

(** Mapping an unbounded nat to a bitvector; only used for bvshl and bvshr
  compatibility funs *)
let int2bv_nat (#n: pos) (num: nat): Tot (bv_t n) = U.to_vec (num % pow2 n)

let int2bv_nat_lemma (#n: pos) (num: uint_t n)
    : Lemma
      (ensures (int2bv_nat #n num == int2bv #n num)) =
  assert (num < pow2 n);
  FStar.Math.Lemmas.modulo_lemma num (pow2 n);
  assert (num % pow2 n = num)

let list2bv #n l = S.seq_of_list l
let bv2list #n s = S.seq_to_list s
let list2bv_bij #n a = S.lemma_list_seq_bij a
let bv2list_bij #n a = S.lemma_seq_list_bij a

let bvand = B.logand_vec
let int2bv_logand #n #x #y #z pf =
  inverse_vec_lemma #n (bvand #n (int2bv #n x) (int2bv #n y))

let bvxor = B.logxor_vec
let int2bv_logxor #n #x #y #z pf =
  inverse_vec_lemma #n (bvxor #n (int2bv x) (int2bv y))

let bvor = B.logor_vec
let int2bv_logor #n #x #y #z pf =
  inverse_vec_lemma #n (bvor #n (int2bv x) (int2bv y))

let bvnot = B.lognot_vec
let int2bv_lognot #n #x #y pf =
  inverse_vec_lemma #n (bvnot #n (int2bv x))

(*TODO: specify index functions? *)
let bvshl' (#n: pos) (a: bv_t n) (s: bv_t n): bv_t n =
  B.shift_left_vec #n a (bv2int #n s)
let bvshl (#n: pos) (a: bv_t n) (s: nat): bv_t n =
  bvshl' #n a (int2bv_nat #n s)

let int2bv_shl' #n #x #y #z pf =
  inverse_vec_lemma #n (bvshl' #n (int2bv #n x) (int2bv #n y))
let int2bv_shl #n #x #y #z pf =
  int2bv_nat_lemma #n y;
  inverse_vec_lemma #n (bvshl #n (int2bv #n x) y)

let bvshr' (#n: pos) (a: bv_t n) (s: bv_t n): bv_t n =
  B.shift_right_vec #n a (bv2int #n s)
let bvshr (#n: pos) (a: bv_t n) (s: nat) : bv_t n =
  bvshr' #n a (int2bv_nat #n s)
let int2bv_shr' #n #x #y #z pf =
  inverse_vec_lemma #n (bvshr' #n (int2bv #n x) (int2bv #n y))
let int2bv_shr #n #x #y #z pf =
  int2bv_nat_lemma #n y;
  inverse_vec_lemma #n (bvshr #n (int2bv #n x) y)



let bvult #n a b = (bv2int #n a) < (bv2int #n b)

let int2bv_lemma_ult_1 #n a b =
  inverse_num_lemma #n a;
  inverse_num_lemma #n b

let int2bv_lemma_ult_2 #n a b =
  inverse_num_lemma #n a;
  inverse_num_lemma #n b


let bvadd #n a b =
    int2bv #n (U.add_mod (bv2int #n a) (bv2int #n b))
let int2bv_add #n #x #y #z pf =
  inverse_vec_lemma #n (bvadd #n (int2bv #n x) (int2bv #n y))

let bvsub #n a b =
    int2bv #n (U.sub_mod (bv2int #n a) (bv2int #n b))
let int2bv_sub #n #x #y #z pf =
  inverse_vec_lemma #n (bvsub #n (int2bv #n x) (int2bv #n y))

let bvdiv #n a b =
    int2bv #n (U.udiv #n (bv2int #n a) b)
let int2bv_div #n #x #y #z pf =
  inverse_vec_lemma #n (bvdiv #n (int2bv #n x) y)

let bvdiv_unsafe #n a b = if (bv2int b <> 0) then bvdiv a (bv2int b) else int2bv 0
let bvdiv_unsafe_sound #n #a #b b_nonzero_pf = ()


let bvmod #n a b =
    int2bv #n (U.mod #n (bv2int #n a) b)
let int2bv_mod #n #x #y #z pf =
  inverse_vec_lemma #n (bvmod #n (int2bv #n x) y)

let bvmod_unsafe #n a b = if (bv2int b <> 0) then bvmod a (bv2int b) else int2bv 0
let bvmod_unsafe_sound #n #a #b b_nonzero_pf = ()

// Z3's bvmul is also modulo
let bvmul #n a b =
  int2bv #n (U.mul_mod #n (bv2int #n a) b)
let int2bv_mul #n #x #y #z pf =
  inverse_vec_lemma #n (bvmul #n (int2bv #n x) y)

let bvmul' #n a b =
  int2bv #n (U.mul_mod #n (bv2int #n a) (bv2int #n b))

let int2bv_mul' #n #x #y #z pf =
  inverse_vec_lemma #n (bvmul' #n (int2bv #n x) (int2bv #n y))
