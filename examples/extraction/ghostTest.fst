(*--build-config
  variables:LIB=../../lib;
  other-files: $LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/ghost.fst $LIB/list.fst
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


assume val effectfulIncr : nat -> nat

val someNat : nat -> nat
let someNat n =
  let _ = (hide (effectfulIncr n)) in n

assume val pureIncr : nat -> Tot nat

val someNat2 : nat -> nat
let someNat2 n =
  let _ = (hide (pureIncr n)) in n
