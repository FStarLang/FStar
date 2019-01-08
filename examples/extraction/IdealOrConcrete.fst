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
module IdealOrConcrete
open Flags

type data (i:id) = 
  | MkData : r:(if ideal i then ref nat else unit) -> data i

val create: i:id -> St (data i)
let create i = 
  if ideal i 
  then MkData (alloc (0<:nat)) //NS: seem to require the <: nat annotation; otherwise infers int and fails
  else MkData ()


val read : #i:id -> data i -> St nat
let read #i d = 
  match d with 
    | MkData r -> 
      if ideal i 
      then !r
      else 0

val write: #i:id -> d:data i -> n:nat -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> if ideal i 
		        then modifies (Set.singleton (Heap.Ref #nat (MkData.r d))) h0 h1  //NS: need the #nat here o.w. implicit arguments fail
			else h0=h1))
let write #i (MkData r) n = 
  if ideal i 
  then (FStar.ST.recall #nat r; //NS: need the #nat here o.w. implicit arguments fail
        r := n)
  else ()
  
