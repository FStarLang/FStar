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
  (loop_inv:(context.R.t  -> nat -> Type))
  (f: (i:U32.t{U32.v i < A.vlength b} -> x:a -> RST.RST unit
    (context)
    (fun _ -> context)
    (fun old -> loop_inv (old context) (U32.v i))
    (fun old _ modern -> loop_inv (modern context) (U32.v i + 1))
  ))
  (len: U32.t{len = A.length b})
  : RST.RST unit
    (R.(AR.array_resource b <*> context))
    (fun _ -> R.(AR.array_resource b <*> context))
    (fun old -> loop_inv (old context) 0)
    (fun old _ modern -> loop_inv (modern context) (A.vlength b) /\
      old (AR.array_resource b) == modern (AR.array_resource b)
    )
