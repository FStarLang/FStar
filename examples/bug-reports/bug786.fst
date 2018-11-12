module Bug786

let f (#a:Type) (x:a) =
  let rec g (#a:Type) (x:a) = unit in
  g x
