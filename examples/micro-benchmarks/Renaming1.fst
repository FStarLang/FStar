module Renaming1

let test (x:int) =
  [@inline_let]
  let s = "essai" in
  [@(rename_let s)]
  let y = x + 1 in
  let essai = y + 2 in
  let z = x + y in
  y + essai
