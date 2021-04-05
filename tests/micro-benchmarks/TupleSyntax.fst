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

(* non-dependent tuples: (t & t') *)
let f1 (x: int & int) : int = fst x
let f2 (x: int & (int & int)) : int = fst x
let f3 (x: int & (int & int)) : int & int = snd x
let f4 (x: int & int & int) : int = let fst, snd, third = x in fst * snd * third
let f5 (x: (int & int) & int) : int = fst (fst x) * snd (fst x) * snd x

(* dependent tuples: (x:t & t') *)
let g1 (x: (x:int & int)) : int = dfst x
let g2 (x: (x:int & (int & int))) : int = dfst x
let g3 (x: (x:int & (y:int & int))) : (y:int & int) = dsnd x
let g4 (x: (x:int & y:int & int)) : int = let (|fst, snd, third|) = x in fst * snd * third
let g5 (x: (x:(int & int) & int)) : int = fst (dfst x) + snd (dfst x) + dsnd x

(* mixed, resolved as dependent tuple *)
let h4 (x: (int & y:int & int)) : int = let (|fst, snd, third|) = x in fst * snd * third
