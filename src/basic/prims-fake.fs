module Prims

type Tot<'a> = 'a

type EqCmp<'a> (eq:'a -> 'a -> bool, hash:'a -> int) =
    interface System.Collections.Generic.IEqualityComparer<'a> with
            member this.Equals(x:'a, y:'a) = eq x y
            member this.GetHashCode(x:'a) = hash x

