module Div

let rec f () : Dv int = f ()

#push-options "--warn_error -272" //Warning_TopLevelEffect
let _ =
  let _ = f () in
  1
#pop-options
