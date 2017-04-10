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
module Tuple

let f x y = (x,y)

let f' x y = (x,y)
let g (x,y) = x
let h (x,y) = (x,y)

let h' (x,y) = y

val f3 : 'a:Type -> 'b:('a => Type) -> 'c:(x:'a => 'b x => Type)
     ->  x:'a -> y:'b x -> 'c x y -> (x:'a * y:'b x * 'c x y)
let f3 x y z = (|x,y,z|)
let g3 (|x,y,z|) = x
let h3 (|x,y,z|) = y
let i3 (|x,y,z|) = z

type ibcf = int * bool * char * float
let quads () : list Tuple.ibcf = 
  let quads = [(0,true,'c',1.0)] in
  (1,false,'d',2.0)::quads

    
(* TODO: pre-typing needs to reason about projection *)
(* val i3' : 'a:Type -> 'b:('a => Type) -> 'c:(x:'a => 'b x => Type) *)
(*      ->  t:(x:'a * y:'b x * 'c x y) -> 'c (MkTuple3._1 t) (MkTuple3._2 t) *)
(* let i3' (x,y,z) = z  *)
