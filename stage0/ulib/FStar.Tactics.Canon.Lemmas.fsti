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
module FStar.Tactics.Canon.Lemmas

open FStar.Mul

val distr : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x * (y + z) == x * y + x * z)

val distl : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) * z == x * z + y * z)

val ass_plus_l : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x + (y + z) == (x + y) + z)

val ass_mult_l : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x * (y * z) == (x * y) * z)

val comm_plus : (#x : int) -> (#y : int) -> Lemma (x + y == y + x)

val sw_plus : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) + z == (x + z) + y)

val sw_mult : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x * y) * z == (x * z) * y)

val comm_mult : (#x : int) -> (#y : int) -> Lemma (x * y == y * x)

val trans : (#a:Type) -> (#x:a) -> (#z:a) -> (#y:a) ->
                    squash (x == y) -> squash (y == z) -> Lemma (x == z)

val cong_plus : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                squash (w == y) -> squash (x == z) ->
                Lemma (w + x == y + z)

val cong_mult : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                squash (w == y) -> squash (x == z) ->
                Lemma (w * x == y * z)

val neg_minus_one : (#x:int) -> Lemma (-x == (-1) * x)

val x_plus_zero : (#x:int) -> Lemma (x + 0 == x)

val zero_plus_x : (#x:int) -> Lemma (0 + x == x)

val x_mult_zero : (#x:int) -> Lemma (x * 0 == 0)

val zero_mult_x : (#x:int) -> Lemma (0 * x == 0)

val x_mult_one : (#x:int) -> Lemma (x * 1 == x)

val one_mult_x : (#x:int) -> Lemma (1 * x == x)

val minus_is_plus : (#x : int) -> (#y : int) -> Lemma (x - y == x + (-y))
