module SepAppK
(* Section 42.6: the downstream unit.  It links against SepLibK's `.cui`, so
   the karamel file it hands to krml must carry SepLibK's declarations as
   [DExternal] and no bodies -- and they must sit in a karamel file *named*
   SepLibK, because karamel names the header it generates after the file and
   not after the lident namespace.  Put them anywhere else and krml writes a
   second header declaring the same symbols, which is the one thing section
   42.2 says a C unit may not do.

   [main] returns nonzero on any wrong answer, so the run is the check. *)

open SepLibK
module U32 = FStar.UInt32
module I32 = FStar.Int32

let main () : I32.t =
  let p = scale ({ px = 5ul; py = 6ul }) in
  (* 10 + 12 *)
  if manhattan p <> 22ul then 1l
  (* SepLibK's global, initialized by its own unit. *)
  else if manhattan origin <> 7ul then 2l
  else if double_it 21ul <> 42ul then 3l
  else 0l
