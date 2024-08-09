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
module GhostTest

open Ghost
open List
type sizedListNonGhost =
| MkSListNG: maxsize:nat->  cont:(list int){length cont < (maxsize)} -> sizedListNonGhost

val aSizedListNG :  sizedListNonGhost
let aSizedListNG = MkSListNG ( 2) [1]

type sizedList =
| MkSList: maxsize:(erased nat)->  cont:(list int){length cont < (reveal maxsize)} -> sizedList

val aSizedList : sizedList
let aSizedList =  MkSList (hide 2) [1]

assume val effectfulIncr : nat -> St nat

val someNat : nat -> nat
let someNat n =
  let _ = (hide (effectfulIncr n)) in n

assume val pureIncr : nat -> Tot nat

val someNat2 : nat -> nat
let someNat2 n =
  let _ = (hide (pureIncr n)) in n

open Heap
type llist : Type -> Type
type rep : #a:Type -> heap -> llist a  -> list a -> Type


val llrev : #a:Type -> l:(llist a) -> el:erased (list a)
    -> ST ((llist a)*(erased (list a)))
        (fun m -> rep m l (reveal el))
        (fun _ rl m1 -> rep m1 (fst rl) (reveal (snd rl)))

let llev l el = admit ()
