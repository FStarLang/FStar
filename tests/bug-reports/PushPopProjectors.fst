module PushPopProjectors

noeq
type t =
 | MkT : a:Type -> a -> t

let test (x:t) : Type = MkT?.a x
let test2 (x:t) (y:MkT?.a x) = 0
