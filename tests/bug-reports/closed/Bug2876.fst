module Bug2876

// Fails since we encode inner let-recs imprecisely.
[@@expect_failure [19]]
let test () =
  assert ((let rec f (x:nat) : Dv nat = f x in f) == (let rec f (x:nat) : Dv nat = f x in f))
