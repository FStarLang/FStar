module NoExtractNorm

let kept (x:nat) = x + 1

noextract
let dropped (x:nat) = x + 1

[@@ noextract_to "krml"]
let dropped_to_krml (x:nat) = x + 1
