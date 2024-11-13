(*
   Copyright 2024 Microsoft Research

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

module PulseCore.PotentiallyErased

val erased : Type u#a -> Type u#a
val reveal #t : erased t -> GTot t
val hide #t (x: t) : y:erased t { reveal y == x }
val bind #t #s (x: erased t) (f: t->erased s) : y: erased s { y == f (reveal x) }

val observe_bool #t (b: erased bool) :
  (squash (reveal b) -> Dv t) ->
  (squash (not (reveal b)) -> Dv t) ->
  Dv t

irreducible let map #t #s (f: t->s) (x: erased t) : y: erased s { reveal y == f (reveal x) } =
  bind x fun x -> hide (f x)