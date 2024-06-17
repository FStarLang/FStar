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
module Unit1.Parser
assume type tint : int -> Type

type t1 = x:int{x >= 0} -> tint x
type t2 = x:int -> tint x
type t3 = (a:eqtype) -> (x:int) -> result:list a{result=[] /\ x=18}
type t4 = x:nat & y:nat{y > x}
type t4' = (x:nat & y:nat{y > x})
type t4'' = (x:nat & (y:nat{y > x})) //parentheses are not significant
type t5 = x:int{x=0} * int
//type t5' = x:int{x=0} * y:int // not allowed after #1905
//type t5' = x:int{x=0} * tint x
//parses but fails name-binding; x is not in scope in the 2nd component
type t6 = (int * int) -> int
type t7 = int * int -> int

//type t8 = x:int * int -> int // not allowed after #1905
//type t8' = x:int * int -> tint x //x is not in scope to the right of the arrow
type t8' = x:(int * int) -> tint (fst x)

type t9 = x:int & tint x -> int
type t9' = y:(x:int & tint x) -> tint (dfst y)

type ta = (x:int) -> (y:int -> tint y) -> tint x
type tb = x:int -> (y:int -> tint y) -> tint x
type tc = x:int -> f:(y:int -> Tot int) -> tint (f 0)

let f1 (x: (y:int &  z:tint y{z==z /\ y=0})) = x
let f2 (x: (  int *  z:tint 0{z==z})) = x
//let f2 (x: (y:int *  z:tint 0{z==z})) = x // not allowed after #1905
let f3 (x: (y:int -> z:tint y{z==z /\ y=0})) = x
let f4 (#a:Type) (l:list a) (#x:int) (v:tint x) = l
let f5 (l:list int) (v:tint 0) = f4 l v

type s0 (x:int) (y:int -> Tot int) = tint (y 0)
type s1 (x: (y:int &  z:tint y{z==z /\ y=0})) = tint (dfst x)
type s2 (x: (  int *  z:tint 0{z==z})) = tint (fst x)
//type s2 (x: (y:int *  z:tint 0{z==z})) = tint (fst x) // not allowed after #1905
type s3 (x: (y:int -> z:tint y{z==z /\ y=0})) = tint ((fun x -> 0) x)

