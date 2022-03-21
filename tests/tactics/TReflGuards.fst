module TReflGuards

open FStar.Tactics

[@@expect_failure]
let _ = assert (x:int{0 <= x} == nat) by begin
  trefl ();
  ()
end

let _ = assert (x:int{0 <= x} == nat) by begin
  trefl_guard ();
  ()
end

let _ = assert true by begin
  if unify (`(x:int{b2t (0 = x)})) (`nat)
  then fail ""
  else ()
end

let _ = assert true by begin
  if unify_guard (`(x:int{b2t (0 <= x)})) (`nat)
  then ()
  else fail ""
end
