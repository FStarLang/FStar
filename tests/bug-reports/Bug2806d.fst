module Bug2806d

open FStar.Tactics

let dom (t:term{exists b c. inspect_ln t == Tv_Arrow b c}) =
  match inspect_ln t with
  | Tv_Arrow b _ -> bv_of_binder b

let idx (t:term{Tv_Arrow? (inspect_ln t)}) : int =
  assert (Tv_Arrow? (inspect_ln t));
  let b : bv = dom t in
  let bv : bv_view = inspect_bv b in
  bv.bv_index

let t1 : (t:term{Tv_Arrow? (inspect_ln t)}) = (`(x:int -> int))
let t2 : (t:term{Tv_Arrow? (inspect_ln t)}) = (`(x:int -> int))

[@@expect_failure]
let falso () : Lemma False =
  assert (t1 == t2) by (compute ());
  assert_norm (idx t1 =!= idx t2)
