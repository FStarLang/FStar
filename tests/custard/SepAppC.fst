module SepAppC
(* Section 42: the downstream unit.  It links against SepLibC's `.cui`, so it
   must emit no definition of [point], no definition of [scale] and no
   definition of [manhattan] -- and must reach them through the header it
   includes instead.  [double_it] was [static] upstream and so is not on
   offer; this unit compiles its own copy of it, which is the cost section
   42.1 describes and not a failure.

   [main] returns nonzero on any wrong answer, so the run is the check. *)

open SepLibC
module U32 = FStar.UInt32

let main () : U32.t =
  let p = scale ({ px = 5ul; py = 6ul }) in
  (* 10 + 12 *)
  if manhattan p <> 22ul then 1ul
  (* SepLibC's global, initialized by its own unit's initializer: 3 + 4. *)
  else if manhattan origin <> 7ul then 2ul
  else if double_it 21ul <> 42ul then 3ul
  else 0ul
