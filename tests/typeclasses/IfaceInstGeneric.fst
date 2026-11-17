module IfaceInstGeneric
open IfaceInstClass
instance generic (a:Type) : c a = { f = (fun _ -> 0) }
