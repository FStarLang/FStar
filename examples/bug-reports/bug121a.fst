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
module Bug121a

val apply : ('a -> Tot 'b) -> 'a -> Tot 'b
let apply f x = f x

val dec : nat -> Tot nat
let rec dec x =
  match x with
  | 0 -> 0
  | _ -> 1 + apply dec (x-1)

val should_be_trivial : x:nat{x>0} -> Lemma
  (ensures (dec x = 1 + apply dec (x-1)))
let should_be_trivial x = ()
