module FStar.Pervasives.Native.Tuple10
open Prims

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j *)
type tuple10 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j =
  | Mktuple10: _1:'a
            -> _2:'b
            -> _3:'c
            -> _4:'d
            -> _5:'e
            -> _6:'f
            -> _7:'g
            -> _8:'h
            -> _9:'i
            -> _10:'j
           -> tuple10 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j
