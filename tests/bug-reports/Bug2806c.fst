module Bug2806c

open FStar.Tactics

let dom (t:term{exists b c. inspect_ln t == Tv_Arrow b c}) =
  match inspect_ln t with
  | Tv_Arrow b _ -> bv_of_binder b

(* This now has to be a sealed string, so the falso() below will just
fail to typecheck the assert. *)
let name (t:term{Tv_Arrow? (inspect_ln t)}) : sealed string =
  assert (Tv_Arrow? (inspect_ln t));
  let b : bv = dom t in
  let bv : bv_view = inspect_bv b in
  bv.bv_ppname

let t1 : (t:term{Tv_Arrow? (inspect_ln t)}) = (`(x:int -> int))
let t2 : (t:term{Tv_Arrow? (inspect_ln t)}) = (`(y:int -> int))

[@@expect_failure]
let falso () : Lemma False =
  assert (t1 == t2) by (compute ());
  assert_norm (name t1 =!= name t2)
