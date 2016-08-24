include MkPrims.Make(struct

  type nonrec int = int
  let ( + ) = ( + )
  let ( - ) = ( - )
  let ( * ) = ( * )
  let ( / ) = ( / )
  let ( <= ) = ( <= )
  let ( >= ) = ( >= )
  let ( < ) = ( < )
  let ( > ) = ( > )
  let ( mod )     = ( mod )
  let ( ~- ) x = - x
  let parse_int  = int_of_string
  let to_string = string_of_int
  let (mod) = (mod)
end)
