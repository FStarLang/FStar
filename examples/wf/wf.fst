(*
   Copyright 2015 Chantal Keller and Catalin Hritcu, Microsoft Research and Inria

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


module Wf


type acc (a:Type) (r:(a -> a -> Type)) (x:a) : Type =
  | AccIntro : (y:a -> r y x -> acc a r y) -> acc a r x

type well_founded (a:Type) (r:(a -> a -> Type)) = x:a -> acc a r x

val acc_inv : r:('a -> 'a -> Type) -> x:'a -> acc 'a r x ->
              y:'a -> r y x -> acc 'a r y
let acc_inv _ = function | AccIntro _ h1 -> h1

val fix_F : r:('a -> 'a -> Type) -> p:('a -> Type) ->
            (x:'a -> (y:'a -> r y x -> p y) -> p x) ->
            x:'a -> acc 'a r x -> p x
let rec fix_F f x a =
  f x (fun y h -> fix_F f y (acc_inv x a y h))

val fix : r:('a -> 'a -> Type) -> well_founded 'a r -> p:('a -> Type) ->
          (x:'a -> (y:'a -> r y x -> p y) -> p x) -> x:'a -> p x
let fix rwf f x = fix_F f x (rwf x)
