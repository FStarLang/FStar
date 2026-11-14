module Bug4244

open FStar.Real

let rexp (x:real) : (x:real{x >. 0.0R}) = admit() (* assumed *)

let rexp_injective (x y : real)
  : Lemma (ensures rexp x == rexp y ==> x == y)
  = admit() (* basic property, assumed *)

[@@expect_failure [19]]
let falso () : False =
  rexp_injective 1.0R 2.0R;
  assert False

// Should not crash
[@@expect_failure [19]]
let tst (g : string) : unit =
  let goal = "A" in
  let x : int = magic () in
  assert (g == goal);
  ()
