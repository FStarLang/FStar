module Renaming2

inline_for_extraction
noextract
let test (s: string) (x:int) =
  [@(rename_let s)]
  let y = x + 1 in
  let essai = y + 2 in
  let z = x + y in
  y + essai

let test2 (x: int) = test "essai" x
