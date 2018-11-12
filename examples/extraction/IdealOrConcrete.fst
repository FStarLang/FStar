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
  
