module Bug2684d

open FStar.Tactics

val f : (#[exact (`1)] _ : int) -> Type0
let f #_ = unit

let elim (d : (y:f & z:unit{y == z} & w:unit{w == z})) : unit =
  match d with
  | Mkdtuple3 #_ #_ #_ x y z -> ()
