open Prims
type ('a, 'b, 'f) is_inj = unit
type ('a, 'b, 'f) is_surj = unit
type ('a, 'b, 'f, 'y) in_image = unit
type ('a, 'b, 'f) image_of = 'b
type 'a powerset = 'a -> Prims.bool