module Bug2806c

open FStar.Tactics

let dom (t:term{exists b c. inspect_ln t == Tv_Arrow b c}) =
  match inspect_ln t with
  | Tv_Arrow b _ -> bv_of_binder b

let name (t:term{Tv_Arrow? (inspect_ln t)}) : Tac string =
  assert (Tv_Arrow? (inspect_ln t));
  let b : bv = dom t in
  let bv : bv_view = inspect_bv b in
  bv_ppname b

let t1 : (t:term{Tv_Arrow? (inspect_ln t)}) = (`(x:int -> int))
let t2 : (t:term{Tv_Arrow? (inspect_ln t)}) = (`(y:int -> int))

//
// bv_ppname is no longer Tot,
//   so we get an error that assert itself is not well-typed
//
[@@expect_failure]
let falso () : Lemma False =
  assert (t1 == t2) by (compute ());
  assert_norm (name t1 =!= name t2)
