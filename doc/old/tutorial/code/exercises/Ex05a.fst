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
module Ex05a
//reverse-ok

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse : list 'a -> Tot (list 'a)
let rec reverse l =
  match l with
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]

val rev : l1:list 'a -> l2:list 'a -> Tot (list 'a) (decreases l2)
let rec rev l1 l2 =
  match l2 with
  | []     -> l1
  | hd::tl -> rev (hd::l1) tl

val append_assoc : xs:list 'a -> ys:list 'a -> zs:list 'a -> Lemma
      (ensures (append (append xs ys) zs == append xs (append ys zs)))
let rec append_assoc xs ys zs =
  match xs with
  | [] -> ()
  | x::xs' -> append_assoc xs' ys zs

val rev_is_ok : l:list 'a -> Lemma (rev [] l == reverse l)

