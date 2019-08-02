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
module Bug517

open FStar.ST

type new_int (z:int) = x:int{x = z}

val add:  new_int 1 -> new_int 2 -> Tot (new_int 3)
let add a b = a + b

let add' (a:new_int 1) (b:new_int 2) : Tot (new_int 3) = a + b


assume new type foo : Type0
noeq abstract type bar = | Cons: foo -> bar
type bar' = bar
type tt = ref bar

(*
type rfoo = ref foo

abstract type bar = | Cons: v:int -> bar | None

assume new type bar : Type0

abstract type foo = | Cons2: v:bar -> foo



(*


open FStar.UInt.UInt32

(*
val test: ref uint32 -> ref uint64 -> Tot unit
let test x y =
  assert(x =!= y)
*)

type lalala = ref banana

type foo = uint32
type bar = uint64

val test: ref foo -> ref bar -> Tot unit
let test x y =
  assert(x =!= y)

type la = uint31
type lala = uint63

(*
val test2 : ref uint31 -> ref uint63 -> Tot unit
let test2 x y = 
  assert(x =!= y)
*)

val test3 : ref la -> ref lala -> Tot unit
let test3 x y = 
  assert(x =!= y)

(*
Bug ?
let test (x:ref uint32) (y:ref uint64) : Tot unit =
  assert(x == y)
*)

let test (x:ref (uint 32)) (y:ref (uint 31)) : Tot unit =
  assert(x =!= y)

let test (x:uint63) (y:uint63) : Tot unit = 
  let x = () in
//  let n = magic() in let m = magic() in
//  assume (n = 2 /\ m = 3);
//  assert(uint n =!= uint m);
  let (x:ref (uint 2)) = magic () in 
  let (y:ref (uint 3)) = magic () in 
  assert(x =!= y); admit()
  assert(uint63 == uint63);
  ()
