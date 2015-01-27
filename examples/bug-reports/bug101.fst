module Fail

type Any (a:Type) : a -> Type = fun (x:a) -> True
assume type t (a:Type) (p:(a -> Type)) : Type

type node (a:Type) : Type =
  | Node : v: (t (node a) (Any (node a))) -> node a

val nodev : node 'a ->  (t (node 'a) (Any (node 'a)) )
let nodev n = match n with | Node v -> v
