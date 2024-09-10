module Div

let rec f () : Dv int = f ()

let _ =
  let _ = f () in
  1
