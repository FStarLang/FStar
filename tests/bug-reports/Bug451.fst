module Bug451

let return_squash = 42

open FStar.Squash

let _ = assert (Bug451.return_squash == 42)
