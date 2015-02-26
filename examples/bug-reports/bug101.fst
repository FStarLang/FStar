module Bug101

type Any (zz:Type) = fun (x:zz) -> True
assume type t (bb:Type) (p:(bb -> Type)) : Type

type node (gg:Type) = 
  | Node : v:t (node gg) (Any (node gg)) -> node gg

val nodev : a:Type -> node a ->  t (node a) (Any (node a))
let nodev (n:node 'a) = match n with 
  | Node v -> v
