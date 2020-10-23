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
