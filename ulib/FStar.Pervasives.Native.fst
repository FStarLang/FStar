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
module FStar.Pervasives.Native
open Prims

type option (a:Type) =
  | None : option a
  | Some : v:a -> option a

(* 'a * 'b *)
type tuple2 'a 'b =
  | Mktuple2: _1:'a -> _2:'b -> tuple2 'a 'b

let fst (x:tuple2 'a 'b) :'a = Mktuple2?._1 x

let snd (x:tuple2 'a 'b) :'b = Mktuple2?._2 x

(* 'a * 'b * 'c *)
type tuple3 'a 'b 'c =
  | Mktuple3: _1:'a
           -> _2:'b
           -> _3:'c
          -> tuple3 'a 'b 'c

(* 'a * 'b * 'c * 'd *)
type tuple4 'a 'b 'c 'd =
  | Mktuple4: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> tuple4 'a 'b 'c 'd

(* 'a * 'b * 'c * 'd * 'e *)
type tuple5 'a 'b 'c 'd 'e =
  | Mktuple5: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> tuple5 'a 'b 'c 'd 'e

(* 'a * 'b * 'c * 'd * 'e * 'f *)
type tuple6 'a 'b 'c 'd 'e 'f =
  | Mktuple6: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> tuple6 'a 'b 'c 'd 'e 'f

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g *)
type tuple7 'a 'b 'c 'd 'e 'f 'g =
  | Mktuple7: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> _7:'g
           -> tuple7 'a 'b 'c 'd 'e 'f 'g

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h *)
type tuple8 'a 'b 'c 'd 'e 'f 'g 'h =
  | Mktuple8: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> _7:'g
           -> _8:'h
           -> tuple8 'a 'b 'c 'd 'e 'f 'g 'h

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
