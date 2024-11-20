module Bug2876

// Fails since we cannot currently encode inner let-recs.
// The original issue was that this crashed, though, so we are indeed
// testing that we get a proper error.
[@@expect_failure [142]]
let test () =
  assert ((let rec f (x:nat) : Dv nat = f x in f) == (let rec f (x:nat) : Dv nat = f x in f))
