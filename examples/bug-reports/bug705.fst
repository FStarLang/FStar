module Bug705

let st (h:Type) (a:Type) =
  h -> M (a * h)

  val return_st : (h:Type) -> (a:Type) -> a -> st h a
  let return_st h a x = fun s -> x, s
