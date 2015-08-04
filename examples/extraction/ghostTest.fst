(*--build-config
  variables:LIB=../../lib;
  other-files: $LIB/ghost.fst $LIB/list.fst
  --*)


module GhostTest

open Ghost
open List
type sizedListNonGhost =
| MkSListNG: maxsize:nat->  cont:(list int){length cont < (maxsize)} -> sizedListNonGhost

val aSizedListNG :  sizedListNonGhost
let aSizedListNG = MkSListNG ( 2) [1]

type sizedList =
| MkSList: maxsize:(ghost nat)->  cont:(list int){length cont < (reveal maxsize)} -> sizedList

val aSizedList : unit -> GTot sizedList
let aSizedList u = let h2 = (hide 2) in MkSList h2 [1]
