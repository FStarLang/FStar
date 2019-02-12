module FStar.Pervasives.Native.Tuple9
open Prims

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i *)
type tuple9 'a 'b 'c 'd 'e 'f 'g 'h 'i =
  | Mktuple9: _1:'a
            -> _2:'b
            -> _3:'c
            -> _4:'d
            -> _5:'e
            -> _6:'f
            -> _7:'g
            -> _8:'h
            -> _9:'i
           -> tuple9 'a 'b 'c 'd 'e 'f 'g 'h 'i
