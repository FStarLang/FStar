include MkPrims.Make(struct

  type int      = Big_int_Z.big_int
  let ( + )     = Big_int_Z.add_big_int
  let ( - )     = Big_int_Z.sub_big_int
  let ( * )     = Big_int_Z.mult_big_int
  let ( / )     = Big_int_Z.div_big_int
  let ( <= )    = Big_int_Z.le_big_int
  let ( >= )    = Big_int_Z.ge_big_int
  let ( < )     = Big_int_Z.lt_big_int
  let ( > )     = Big_int_Z.gt_big_int
  let ( mod )     = Big_int_Z.mod_big_int
  let ( ~-)     = Big_int_Z.minus_big_int
  let parse_int = Big_int_Z.big_int_of_string

end)
