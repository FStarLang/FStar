module Bug2806c

open FStar.Tactics
module R = FStar.Reflection

let dom (t:term{exists b c. inspect_ln t == R.Tv_Arrow b c}) : R.binder =
  match inspect_ln t with
  | R.Tv_Arrow b _ -> b

let name (t:term{R.Tv_Arrow? (inspect_ln t)}) : Tac string =
  assert (R.Tv_Arrow? (inspect_ln t));
  let b : R.binder = dom t in
  unseal (inspect_binder b).ppname

let t1 : (t:term{R.Tv_Arrow? (inspect_ln t)}) = (`(x:int -> int))
let t2 : (t:term{R.Tv_Arrow? (inspect_ln t)}) = (`(y:int -> int))

//
// name_of_bv is no longer Tot,
//   so we get an error that assert itself is not well-typed
//
[@@expect_failure]
let falso () : Lemma False =
  assert (t1 == t2) by (compute ());
  let n1 = name t1 in
  let n2 = name t2 in
  assert_norm (n1 =!= n2)
