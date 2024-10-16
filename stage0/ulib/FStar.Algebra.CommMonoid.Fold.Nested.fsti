(*
   Copyright 2022 Microsoft Research
   
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
   
       http://www.apache.org/licenses/LICENSE-2.0
       
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: A. Rozanov
*)

(*
   Here we reason about nested folds of functions over arbitrary 
   integer intervals. We call such functions generators.
*)
 
module FStar.Algebra.CommMonoid.Fold.Nested

module CF = FStar.Algebra.CommMonoid.Fold
module CE = FStar.Algebra.CommMonoid.Equiv

open FStar.IntegerIntervals 

(* This constructs a generator function that has its arguments in reverse 
   order. Useful when reasoning about nested folds, transposed matrices, etc. 
   
   Note how this utility is more general than transposed_matrix_gen 
   found in FStar.Seq.Matrix -- but for zero-based domains, latter is 
   more convenient. *)
let transpose_generator #c (#m0 #mk: int)
                          (#n0 #nk: int)
                          (gen: ifrom_ito m0 mk -> ifrom_ito n0 nk -> c)
  : (f: (ifrom_ito n0 nk -> ifrom_ito m0 mk -> c) { forall i j. f j i == gen i j })
  = fun j i -> gen i j
  
let double_fold #c #eq #a0 (#ak: not_less_than a0) #b0 (#bk:not_less_than b0)
                (cm: CE.cm c eq)
                (g: ifrom_ito a0 ak -> ifrom_ito b0 bk -> c) = 
  CF.fold cm a0 ak (fun (i: ifrom_ito a0 ak) -> CF.fold cm b0 bk (g i))  


(* Most general form of nested fold swap theorem. Here we prove that we can 
   exchange the order of nested foldings over any suitable generator function. *)
val double_fold_transpose_lemma (#c:_) (#eq: _)
                                (#m0: int) (#mk: not_less_than m0)
                                (#n0: int) (#nk: not_less_than n0)
                                (cm: CE.cm c eq) 
                                (offset_gen: ifrom_ito m0 mk -> ifrom_ito n0 nk -> c)
  : Lemma (double_fold cm offset_gen
           `eq.eq`            
           double_fold cm (transpose_generator offset_gen))
