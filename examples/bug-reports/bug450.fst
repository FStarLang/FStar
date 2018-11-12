module Bug450

let what =
  let rec g (x:int) : Dv int =
    h x
  and h : int -> Dv int =
    g
  in
  g 0
