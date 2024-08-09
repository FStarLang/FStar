module Bug3130

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

open FStar.Tactics.Typeclasses

//#set-options "--debug Low"

noeq
type machin (a:Type) (d : typeclass2 bytes #solve a) (content:a) = {
  lemma:
   unit ->
    Lemma
    (ensures truc #bytes #bytes_typeclass1_ #a #solve t_inst content) // error here on `truc`
  ;
}
