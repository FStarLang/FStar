include MkPrims.Make(struct

  type int = Big_int.big_int
  let ( + )     = Big_int.add_big_int
  let ( - )     = Big_int.sub_big_int
  let ( * )     = Big_int.mult_big_int
  let ( / )     = Big_int.div_big_int
  let ( <= )    = Big_int.le_big_int
  let ( >= )    = Big_int.ge_big_int
  let ( < )     = Big_int.lt_big_int
  let ( > )     = Big_int.gt_big_int
  let ( % )     = Big_int.mod_big_int
  let op_Minus  = Big_int.minus_big_int
  let parse_int = Big_int.big_int_of_string

end)
