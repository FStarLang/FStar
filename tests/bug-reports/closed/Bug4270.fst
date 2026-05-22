module Bug4270

open FStar.Real

// assume val ( >.  ) : real -> real -> prop

let test (p : prop) =
  assume p;
  assert (has_type p prop);
  assert (t2b p == true)

let test' (x y : int) =
  assume (x > y);
  assert (has_type (x > y) bool);
  assert (t2b (x > y) == true);
  ()

let test'' (x y : real) =
  assume (x >. y);
  assert (has_type (x >. y) prop);
  assert (t2b (x >. y) == true)

let rmax (x y: real) : real =
  if x >. y then x else y

let lem_rmax_comm (x y : real)
  : Lemma (requires x >. y)
          (ensures rmax x y == x)
  = assert (x >. y);
    assert (t2b (x >. y) == true);
    assert (t2b (x >. y));
    ()

let lem_rmax_comm' (x y : real)
  : Lemma (requires x >. y)
          (ensures rmax x y == x)
  = ()

// This only succeeds since we have primitive knowledge of >.
let test_basic (x : real{ x >. 1.0R }) =
  assert (x >. 0.0R)
