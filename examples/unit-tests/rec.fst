(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module Foo.Record


let foo x y = if x <= y && y <= x then 0 else 1

type r = {
  a:int; 
  b:int;
}

let matchr r = match r with 
  | ({a=_}) -> 1

type pair = {x:int; y:int}
and triple = {fst:pair; z:int}

let mkR i j = {a=i; b=j}
let mkPair i j = {x=i; y=j}
let mkFoo i = {fst={x=i; y=i}; z=i}

let a x = x.a
let f x y = {x=x; y=y}
let g p = p.x
let h p = p.y
let i p = match p with
  | {fst=_} -> ""

let rec even x = x=0 || not (odd (x - 1))
and odd x = x=1 || not (even (x - 1))

