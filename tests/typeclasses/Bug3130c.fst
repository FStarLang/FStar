module Bug3130c

open FStar.Tactics.Typeclasses

class typeclass1 (a:Type0) = {
  x: unit;
}

class typeclass2 (bytes:Type0) {|typeclass1 bytes|} (a:Type) = {
  y:unit;
}

assume val bytes: Type0
assume val bytes_typeclass1: typeclass1 bytes
instance bytes_typeclass1_ = bytes_typeclass1
assume val t: Type0 -> Type0
assume val t_inst: t bytes

assume val truc:
  #bytes:Type0 -> {|typeclass1 bytes|} ->
  #a:Type -> {|typeclass2 bytes a|} ->
  t bytes -> a ->
  Type0

noeq
type machin (a:Type) {|typeclass2 bytes a|} = {
  pred: a -> prop;
  lemma:
    content:a ->
    Lemma
    (ensures truc t_inst content)
  ;
}

let pre (#a:Type) {|d : typeclass2 bytes a|}
        (m : machin a) (x : a)
        = m.pred x

val bidule:
  #a:Type -> {|typeclass2 bytes a|} ->
  m:machin a -> x:a ->
  Lemma
  (requires m.pred x)
  (ensures True)
let bidule #a #tc2 m x = ()
