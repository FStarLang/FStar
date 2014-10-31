module Prims

(* Needed to make bootstraping working (boot target of the Makefile);
   but when we actually type-check this within F*, we have the right
   definition of totality *)
type Tot<'a> = 'a

type EqCmp<'a> (eq:'a -> 'a -> bool, hash:'a -> int) =
    interface System.Collections.Generic.IEqualityComparer<'a> with
            member this.Equals(x:'a, y:'a) = eq x y
            member this.GetHashCode(x:'a) = hash x

type Boxed<'a> (value:'a, cmp:'a -> 'a -> int, hash: 'a -> int) = 
   member this.unbox = value
   override this.Equals (other:obj) = let y = other :?> Boxed<'a> in cmp value (y.unbox) = 0
   override this.GetHashCode() = hash value
   interface System.IComparable with
            member this.CompareTo(other:obj) = 
                let x = other :?> Boxed<'a> in 
                cmp value (x.unbox)
