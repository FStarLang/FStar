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
module TupleSyntax
open FStar.Mul

/// The operator [&] is overloaded and might denotes:
///  - dependent tuples ([dtuple2], [dtuple3], ...)
///  - non-dependent tuples ([tuple2], [tuple3], ...)
///
/// The operator [&] is desugared into a non-dependent tuple whenever
/// it is possible to, that is, whenever there is no actual
/// dependency. Otherwise, the tuple is desugared as a dependent
/// tuple.

(** Non-dependent tuples *)
let f1 (x: int & int) : int = fst x
let f2 (x: int & (int & int)) : int = fst x
let f3 (x: int & (int & int)) : int & int = snd x
let f4 (x: int & int & int) : int = let fst, snd, third = x in fst * snd * third
let f5 (x: (int & int) & int) : int = fst (fst x) * snd (fst x) * snd x
let f6 (x: (x:int & int)) : int = fst x
let f7 (x: (x:int & y:int {y > 0})) : int = fst x

(** Dependent tuples *)
let g1 (x: (x:int & y:int {x > 3})) : int = dfst x
let g2 (x: (x:int & y:int {x > 3} & z:int {y>z})) : int = let (|x,y,z|) = x in 0
// [g3]'s last component [z] doesn't depends on [x] or [y], but since
// [y] depends on [x], it's a dependent tuple anyway
let g3 (x: (x:int & y:int {x > 3} & z:int)) : int = let (|x,y,z|) = x in x
let g4 (x: (x:int & (y:int {x > 3} & z:int))) : int = let (|x,(y,z)|) = x in x
let g5 (x: (x:int & y:int {x > 3}) & int) : int = let ((|x,y|),z) = x in x
let g6 (x y: unit) (t: (x:int & y:int {x > y})) = let (|x, y|) = t in x
