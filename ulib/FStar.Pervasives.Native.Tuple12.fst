module FStar.Pervasives.Native.Tuple12
open Prims


(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l *)
type tuple12 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l =
  | Mktuple12: _1:'a
            -> _2:'b
            -> _3:'c
            -> _4:'d
            -> _5:'e
            -> _6:'f
            -> _7:'g
            -> _8:'h
            -> _9:'i
            -> _10:'j
            -> _11:'k
            -> _12:'l
           -> tuple12 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l
