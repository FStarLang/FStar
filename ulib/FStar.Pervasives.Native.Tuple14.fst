module FStar.Pervasives.Native.Tuple14
open Prims

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n *)
type tuple14 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n =
  | Mktuple14: _1:'a
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
            -> _14:'n
           -> tuple14 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n
