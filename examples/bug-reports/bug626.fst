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
module Bug626

(* Works *)
val lemma: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [SMTPat (x + y);SMTPat (y + x)]
let lemma x y = ()

val lemma2: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [SMTPatOr [
      [SMTPat (x + y)]];
   SMTPatOr [
       [SMTPat (y + x)]]]
(* Fails *)
(* let lemma2 x y = () *)

(* Works *)
val lemma3: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [SMTPatOr [
      [SMTPat (x + y);
       SMTPat (y + x)]]]
let lemma3 x y = ()

val lemma4: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [SMTPatOr [
      [SMTPat (x + y);
       SMTPat (y + x)]];
   SMTPat (x + y)]
(* Fails *)
(* let lemma4 x y = () *)

(* Works *)
val lemma5: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [SMTPat [SMTPatOr [
      [SMTPat (x + y);
       SMTPat (y + x)]]];
   SMTPat [SMTPat (x + y)]]
let lemma5 x y = ()
