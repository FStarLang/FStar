module FStar.Pervasives.Native.Tuple11
open Prims

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k *)
type tuple11 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k =
  | Mktuple11: _1:'a
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
           -> tuple11 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k
