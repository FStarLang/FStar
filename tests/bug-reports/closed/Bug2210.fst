module Bug2210
//Example from Son Ho

// We don't want to unfold f1
let rec f1 (n : nat) : nat =
  if n = 0 then 0 else n + f1 (n-1)

// We want to unfold f2 in a controlled manner
[@(strict_on_arguments [0])]
noextract
let rec f2 (xs : list nat) (n : nat) : list nat =
  match xs with
  | [] -> []
  | x :: xs' -> f1 n :: f2 xs' n // everything works fine if [f1] is not called here

// When extracting this, we want to make sure that `f1` is not unfolded,
// otherwise we end up in a normalization loop
let f3 x = Pervasives.norm [zeta_full; delta_only[`%f2]; primops; iota] (f2 [1] x)
