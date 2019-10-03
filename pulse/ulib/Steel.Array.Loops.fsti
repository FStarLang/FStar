(*
   Copyright 2008-2019 Microsoft Research

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
module Steel.Array.Loops


open Steel.RST
module A = Steel.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module P = LowStar.Permissions
module U32 = FStar.UInt32
module L = Steel.Loops

open FStar.Mul

val iteri
  (#a: Type0)
  (b: A.array a)
  (context: resource)
  (loop_inv:(rmem context -> nat -> Type))
  (f: (i:U32.t{U32.v i < A.vlength b} -> x:a -> RST unit
    (context)
    (fun _ -> context)
    (fun h0 -> loop_inv h0 (U32.v i))
    (fun h0 _ h1 -> loop_inv h1 (U32.v i + 1))
  ))
  (len: U32.t{len = A.length b})
  : RST unit
    (A.array_resource b <*> context)
    (fun _ -> A.array_resource b <*> context)
    (fun h0 -> loop_inv (focus_rmem h0 #(A.array_resource b) context) 0)
    (fun h0 _ h1 -> loop_inv (focus_rmem h1 #(A.array_resource b) context) (A.vlength b) /\
      h0 (A.array_resource b) ==  h1 (A.array_resource b)
    )
