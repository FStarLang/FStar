(*--build-config
 other-files: FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Ghost.fst FStar.List.fst
  --*)


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
