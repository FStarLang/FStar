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
module LowStar.RST.Array.Loops


module R = LowStar.Resource
module RST = LowStar.RST
module A = LowStar.Array
module AR = LowStar.RST.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module P = LowStar.Permissions
module U32 = FStar.UInt32
module L = LowStar.RST.Loops

open FStar.Mul

val iteri
  (#a: Type0)
  (b: A.array a)
  (context: R.resource)
  (loop_inv:(RST.selector context -> nat -> Type))
  (f: (i:U32.t{U32.v i < A.vlength b} -> x:a -> RST.RST unit
    (context)
    (fun _ -> context)
    (fun old -> loop_inv old (U32.v i))
    (fun old _ modern -> loop_inv modern (U32.v i + 1))
  ))
  (len: U32.t{len = A.length b})
  : RST.RST unit
    (R.(AR.array_resource b <*> context))
    (fun _ -> R.(AR.array_resource b <*> context))
    (fun old -> loop_inv (RST.focus_selector old context) 0)
    (fun old _ modern -> loop_inv (RST.focus_selector modern context) (A.vlength b) /\
      old (AR.array_resource b) == modern (AR.array_resource b)
    )
