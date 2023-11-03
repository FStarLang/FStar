module UnifyStrictArgs

open FStar.Tactics

type t (k:int) = | Mk of (x:int{x > k})

[@@strict_on_arguments [1]]
let f1 k (x:t k) : int = match x with | Mk n -> n

let f2 k (x:t k) : int = match x with | Mk n -> n

[@@strict_on_arguments [1]; tcnorm]
let f3 k (x:t k) : int = match x with | Mk n -> n

[@@strict_on_arguments_unfold [1]; tcnorm]
let f4 k (x:t k) : int = match x with | Mk n -> n

let _ = assert True by begin
  if not (unify (`f1 _) (`f2 42)) then fail "1";
  if not (unify (`f1 _) (`f3 42)) then fail "2";
  if not (unify (`f1 _) (`f4 42)) then fail "3";
  if not (unify (`f2 _) (`f3 42)) then fail "4";
  if not (unify (`f2 _) (`f4 42)) then fail "5";
  if not (unify (`f3 _) (`f4 42)) then fail "6";
  ()
end
