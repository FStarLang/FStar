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
module FStar.Tactics.BV.Lemmas

open FStar.BV
open FStar.UInt

// using uint_t' instead of uint_t breaks the tactic (goes to inl).

(* Congruence lemmas *)
val cong_bvand : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
                   (#y:bv_t n) -> (#z:bv_t n) ->
                   squash (w == y) -> squash (x == z) ->
                   Lemma (bvand #n w x == bvand #n y z)

val cong_bvxor : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
                   (#y:bv_t n) -> (#z:bv_t n) ->
                   squash (w == y) -> squash (x == z) ->
                   Lemma (bvxor w x == bvxor y z)

val cong_bvor : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
                   (#y:bv_t n) -> (#z:bv_t n) ->
                   squash (w == y) -> squash (x == z) ->
                   Lemma (bvor w x == bvor y z)

val cong_bvshl : #n:pos -> (#w:bv_t n) -> (#x:uint_t n) ->
                 (#y:bv_t n) -> squash (w == y) ->
                 Lemma (bvshl w x == bvshl y x)

val cong_bvshr : #n:pos -> #w:bv_t n -> (#x:uint_t n) ->
               #y:bv_t n -> squash (w == y) ->
               Lemma (bvshr #n w x == bvshr #n y x)

val cong_bvdiv : #n:pos -> #w:bv_t n -> (#x:uint_t n{x <> 0}) ->
              #y:bv_t n -> squash (w == y) ->
               Lemma (bvdiv #n w x == bvdiv #n y x)

val cong_bvmod : #n:pos -> #w:bv_t n -> (#x:uint_t n{x <> 0}) ->
              #y:bv_t n -> squash (w == y) ->
               Lemma (bvmod #n w x == bvmod #n y x)

val cong_bvmul : #n:pos -> #w:bv_t n -> (#x:uint_t n) ->
              #y:bv_t n -> squash (w == y) ->
               Lemma (bvmul #n w x == bvmul #n y x)

val cong_bvadd : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
              (#y:bv_t n) -> (#z:bv_t n) ->
              squash (w == y) -> squash (x == z) ->
              Lemma (bvadd w x == bvadd y z)

val cong_bvsub : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
              (#y:bv_t n) -> (#z:bv_t n) ->
              squash (w == y) -> squash (x == z) ->
              Lemma (bvsub w x == bvsub y z)

(* Used to reduce the initial equation to an equation on bitvectors*)
val eq_to_bv: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) ->
              squash (int2bv #n x == int2bv #n y) -> Lemma (x == y)

val lt_to_bv: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) ->
              (b2t (bvult #n (int2bv #n x) (int2bv #n y))) -> Lemma (x < y)

(* Creates two fresh variables and two equations of the form int2bv
   x = z /\ int2bv y = w. The above lemmas transform these two
   equations before finally instantiating them through reflexivity,
   leaving Z3 to solve z = w *)
val trans: #n:pos -> (#x:bv_t n) -> (#y:bv_t n) -> (#z:bv_t n) -> (#w:bv_t n) ->
          squash (x == z) -> squash (y == w) -> squash (z == w) ->
          Lemma (x == y)

val trans_lt: #n:pos -> (#x:bv_t n) -> (#y:bv_t n) -> (#z:bv_t n) -> (#w:bv_t n) ->
          (eq2 #(bv_t n) x z) -> (eq2 #(bv_t n) y w) -> squash (bvult #n z w) ->
          Lemma (bvult #n x y)

val trans_lt2: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) -> (#w:bv_t n) ->
          squash (int2bv #n x == z) -> squash (int2bv #n y == w) -> squash (bvult #n z w) ->
          Lemma (x < y)