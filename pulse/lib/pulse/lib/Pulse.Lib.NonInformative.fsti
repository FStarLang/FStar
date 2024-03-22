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
