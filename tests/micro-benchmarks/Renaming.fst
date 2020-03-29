module Renaming

let test (x:int) =
  [@(rename_let "essai")]
  let y = x + 1 in
  let essai = y + 2 in
  let z = x + y in
  y + essai
