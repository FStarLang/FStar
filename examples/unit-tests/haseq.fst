module Haseq

type l = list int

type t = {
  fld1: x:l{List.Tot.length x > 4};
  fld2: y:l{List.Tot.length y > 5};
}

let foo (x:unit) = assert (hasEq nat)

