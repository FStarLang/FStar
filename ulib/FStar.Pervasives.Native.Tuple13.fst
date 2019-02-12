module FStar.Pervasives.Native.Tuple13
open Prims

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm *)
type tuple13 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm =
  | Mktuple13: _1:'a
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
            -> _13:'m
           -> tuple13 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm
