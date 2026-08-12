module Bug2876

// Inner let-recs are still encoded imprecisely, but the symbol we generate is
// keyed on a hash of the term, so two syntactically equal inner let-recs are
// encoded by the same symbol.
let test () =
  assert ((let rec f (x:nat) : Dv nat = f x in f) == (let rec f (x:nat) : Dv nat = f x in f))

// Two different ones are still indistinguishable from each other.
[@@expect_failure [19]]
let test2 () =
  assert ((let rec f (x:nat) : Dv nat = f x in f) == (let rec f (x:nat) : Dv nat = f (x+1) in f))
