module InlineForExtractionNormRequest

inline_for_extraction noextract
let id (x:'a) = x

let test (x:int) = norm [primops] (id 0 + 1)

inline_for_extraction noextract
val f1 : bool -> bool
let f1 b = not b

/// OK: Normalizes to [not b]
val f2 : bool -> bool
let f2 b = f1 b

/// OK: Normalizes to [not b]
val f3 : bool -> bool
let f3 b = Pervasives.norm [delta_only[]] (f1 b)

/// OK: Normalizes to [not (not b || not (not b))]
val f4 : bool -> bool
let f4 b =
  [@inline_let] let b1 = f1 b in
  [@inline_let] let b2 = f1 (not b) in
  f1 (b1 || b2)

/// OK: Normalizes to [ not ((not b) || (not (not b)))]
val f5 : bool -> bool
let f5 b =
  [@inline_let] let b1 = f1 b in
  [@inline_let] let b2 = f1 (not b) in
  Pervasives.norm [delta_only []] (f1 (b1 || b2))

/// Same, but explicitly asking for NBE. The `for_extraction` flag and the
/// delta level it implies used to be dropped when dispatching to NBE, so
/// `id` and `f1` were left unfolded and extraction failed with error 342.
let test_nbe (x:int) = norm [nbe; primops] (id 0 + 1)

val f3_nbe : bool -> bool
let f3_nbe b = Pervasives.norm [nbe; delta_only []] (f1 b)
