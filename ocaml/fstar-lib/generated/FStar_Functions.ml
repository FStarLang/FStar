open Prims
type ('a, 'b, 'f) is_inj = unit
type ('a, 'b, 'f) is_surj = unit
type ('a, 'b, 'f) is_bij = unit
type ('a, 'b, 'f, 'y) in_image = unit
type ('a, 'b, 'f) image_of = 'b
type ('a, 'b, 'g, 'f) is_inverse_of = unit
type 'a powerset = 'a -> Prims.bool