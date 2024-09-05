module Pulse.Lib.NonInformative

open FStar.Ghost

type revealer (a:Type u#aa) =
  x:Ghost.erased a -> Tot (y:a{y == Ghost.reveal x})

class non_informative (a:Type u#aa) : Type u#aa = {
  reveal : revealer a;
}

instance val non_informative_unit : non_informative unit
instance val non_informative_prop : non_informative prop
instance val non_informative_erased (a:Type) : non_informative (erased a)
instance val non_informative_squash (a:Type) : non_informative (squash a)

instance val non_informative_tuple2
  (a b : Type)
  (_ : non_informative a)
  (_ : non_informative b)
  : non_informative (a & b)

instance val non_informative_tuple3
  (a b c : Type)
  (_ : non_informative a)
  (_ : non_informative b)
  (_ : non_informative c)
  : non_informative (a & b & c)

instance val non_informative_tuple4
  (a b c d : Type)
  (_ : non_informative a)
  (_ : non_informative b)
  (_ : non_informative c)
  (_ : non_informative d)
  : non_informative (a & b & c & d)

instance val non_informative_tuple5
  (a b c d e : Type)
  (_ : non_informative a)
  (_ : non_informative b)
  (_ : non_informative c)
  (_ : non_informative d)
  (_ : non_informative e)
  : non_informative (a & b & c & d & e)

instance val non_informative_tuple6
  (a b c d e f : Type)
  (_ : non_informative a)
  (_ : non_informative b)
  (_ : non_informative c)
  (_ : non_informative d)
  (_ : non_informative e)
  (_ : non_informative f)
  : non_informative (a & b & c & d & e & f)

instance val non_informative_tuple7
  (a b c d e f g : Type)
  (_ : non_informative a)
  (_ : non_informative b)
  (_ : non_informative c)
  (_ : non_informative d)
  (_ : non_informative e)
  (_ : non_informative f)
  (_ : non_informative g)
  : non_informative (a & b & c & d & e & f & g)
