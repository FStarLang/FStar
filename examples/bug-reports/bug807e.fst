module Bug807e

let endo : Type u#(a+1) = Type u#a -> Type u#a
let monad_return (t : endo) = #a:Type -> a -> t a
let monad_bind (t:endo) = #a:Type -> #b:Type -> t a -> (a -> t b) -> t b

noeq
type monad_struct =
  | MkMonad :
    car:endo ->
    ret:monad_return car ->
    bnd:monad_bind car ->
    monad_struct

noeq type monad_laws (s : monad_struct) =
  {
    runit : a:Type -> m:s.car a ->
      Lemma (s.bnd #a m (s.ret (* without #_ it fails*)) == m) ;
  }
