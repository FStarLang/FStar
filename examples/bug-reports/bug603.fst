module Bug603

noeq type r (a:Type) : a -> a -> Type =
| R : (x:a) -> r (* a *) x x
