module Bug2806b

open FStar.Reflection

let non_fun #a #b (f : a -> b) (x y : a) (fx fy : b) :
  Lemma (requires f x == fx /\ f y == fy /\ x == y)
        (ensures fx == fy) = ()

[@@expect_failure]
let test () : Lemma False =
    let t1 = (`(2 <: int)) in
    let t2 = (`2) in
    assert (t1 == t2);
    let tv1 = inspect_ln t1 in
    let tv2 = inspect_ln t2 in
    assert (tv1 =!= tv2);
    non_fun inspect_ln t1 t2 tv1 tv2 // nudge SMT
