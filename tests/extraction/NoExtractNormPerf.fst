module NoExtractNormPerf

(* Each level doubles when extraction normalization unfolds
   [inline_for_extraction] definitions. At level 18, the compact term below
   expands to more than 250,000 applications. None of that work is useful:
   every definition in this module is dropped by extraction. *)

inline_for_extraction noextract
let d0 (x:nat) : nat = x + 1

inline_for_extraction noextract
let d1 (x:nat) : nat = d0 (d0 x)

inline_for_extraction noextract
let d2 (x:nat) : nat = d1 (d1 x)

inline_for_extraction noextract
let d3 (x:nat) : nat = d2 (d2 x)

inline_for_extraction noextract
let d4 (x:nat) : nat = d3 (d3 x)

inline_for_extraction noextract
let d5 (x:nat) : nat = d4 (d4 x)

inline_for_extraction noextract
let d6 (x:nat) : nat = d5 (d5 x)

inline_for_extraction noextract
let d7 (x:nat) : nat = d6 (d6 x)

inline_for_extraction noextract
let d8 (x:nat) : nat = d7 (d7 x)

inline_for_extraction noextract
let d9 (x:nat) : nat = d8 (d8 x)

inline_for_extraction noextract
let d10 (x:nat) : nat = d9 (d9 x)

inline_for_extraction noextract
let d11 (x:nat) : nat = d10 (d10 x)

inline_for_extraction noextract
let d12 (x:nat) : nat = d11 (d11 x)

inline_for_extraction noextract
let d13 (x:nat) : nat = d12 (d12 x)

inline_for_extraction noextract
let d14 (x:nat) : nat = d13 (d13 x)

inline_for_extraction noextract
let d15 (x:nat) : nat = d14 (d14 x)

inline_for_extraction noextract
let d16 (x:nat) : nat = d15 (d15 x)

inline_for_extraction noextract
let d17 (x:nat) : nat = d16 (d16 x)

inline_for_extraction noextract
let d18 (x:nat) : nat = d17 (d17 x)
