(*--build-config
  options: --admit_fsi FStar.Set;
  other-files: FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
  --*)
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
module FStar.Int32
val min_value_int : int
let min_value_int = -2147483648

val max_value_int : int
let max_value_int = 2147483647

let within_int32 (i:int) =
    min_value_int <= i
    && i <= max_value_int

private type int32 =
  | Int32 : i:int{within_int32 i} -> int32

val min_value : int32
let min_value = Int32 min_value_int

val max_value : int32
let max_value = Int32 max_value_int

val as_int: i:int32 -> GTot int
let as_int (Int32 i) = i

type nat32 = x:int32{Prims.op_GreaterThanOrEqual (as_int x) 0}

//a ?+ b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Plus: i:int32
              -> j:int32
              -> Tot (k:int32{within_int32 (as_int i + as_int j) ==> as_int k = as_int i + as_int j})
let op_Question_Plus (Int32 i) (Int32 j) =
  if within_int32 (i + j)
  then Int32 (i + j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Plus: i:int32
          -> j:int32{within_int32 (as_int i + as_int j)}
          -> Tot int32
let op_Plus (Int32 i) (Int32 j) = Int32 (i + j)

//a ?- b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Subtraction: i:int32
              -> j:int32
              -> Tot (k:int32{within_int32 (as_int i - as_int j) ==> as_int k = as_int i - as_int j})
let op_Question_Subtraction (Int32 i) (Int32 j) =
  if within_int32 (i - j)
  then Int32 (i - j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Subtraction: i:int32
                 -> j:int32{within_int32 (as_int i - as_int j)}
                 -> Tot int32
let op_Subtraction (Int32 i) (Int32 j) = Int32 (i - j)

//a ?* b may overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Star:
                 i:int32
              -> j:int32
              -> Tot (k:int32{within_int32 (as_int i * as_int j) ==> as_int k = as_int i * as_int j})
let op_Question_Star (Int32 i) (Int32 j) =
  if within_int32 (i * j)
  then Int32 (i * j)
  else magic()//mark as admit, because we do not specify the overflow semantics

val op_Star: i:int32
          -> j:int32{within_int32 (as_int i * as_int j)}
          -> Tot int32
let op_Star (Int32 i) (Int32 j) = Int32 (i * j)

//When the dividend is negative, the semantics is platform dependent
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Slash: i:int32
                           -> j:int32{as_int j <> 0}
                           -> Tot (k:int32{as_int i >= 0 ==> as_int k = as_int i / as_int j})
let op_Question_Slash (Int32 i) (Int32 j) =
  if i < 0
  then magic ()//mark as admit, because we do not specify the overflow semantics
  else Int32 (i / j)

//division does not overflow when the dividend is non-negative
val op_Slash: i:int32{as_int i >= 0}
           -> j:int32{as_int j <> 0}
           -> Tot int32
let op_Slash (Int32 i) (Int32 j) = Int32 (i / j)

//a ?% b can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Percent:
                i:int32
             -> j:int32{as_int j <> 0}
             -> Tot (k:int32{not(as_int i = min_value_int && as_int j = -1)
                             ==> as_int k = as_int i % as_int j})
let op_Question_Percent (Int32 i) (Int32 j) =
  if i=min_value_int && j = -1
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int32 (i % j)

//From: http://stackoverflow.com/questions/19285163/does-modulus-overflow
//Overflow can occur during a modulo operation when the dividend is equal to the
//minimum (negative) value for the signed integer type and the divisor is equal
//to -1.
val op_Percent: i:int32
             -> j:int32{as_int j <> 0 /\ not(i = min_value && as_int j = -1)}
             -> Tot int32
let op_Percent (Int32 i) (Int32 j) = Int32 (i % j)

//?- a    can overflow
//must be marked opaque because the body has an intentional admit
opaque val op_Question_Minus: i:int32
                   -> Tot int32
let op_Question_Minus (Int32 i) =
  if i = min_value_int
  then magic()//mark as admit, because we do not specify the overflow semantics
  else Int32 (-i)

val op_Minus: i:int32{i <> min_value}
           -> Tot int32
let op_Minus (Int32 i) = Int32 (-i)

val op_Less_Equals: i:int32
                 -> j:int32
                 -> Tot bool
let op_Less_Equals (Int32 i) (Int32 j) = i <= j

val op_Less: i:int32
          -> j:int32
          -> Tot bool
let op_Less (Int32 i) (Int32 j) = i < j

val op_Greater_Equals: i:int32
                    -> j:int32
                    -> Tot bool
let op_Greater_Equals (Int32 i) (Int32 j) = i >= j

val op_Greater: i:int32
             -> j:int32
             -> Tot bool
let op_Greater (Int32 i) (Int32 j) = i > j
