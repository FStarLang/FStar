module Bug101

type any (zz:Type) = fun (x:zz) -> True
assume type t (bb:Type) (p:(bb -> Type)) : Type

type node (gg:Type) = 
  | Node : v:t (node gg) (any (node gg)) -> node gg

val nodev : a:Type -> node a ->  t (node a) (any (node a))
let nodev (n:node 'a) = match n with 
  | Node v -> v
