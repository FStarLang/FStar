module CherryTiming

(* FStarC.Timing-c.cherry.fst: the clock is monotonic, and [record_ns] and
   [record_ms] return the result of the function and a nonnegative time. *)
open FStarC.Effect
module T = FStarC.Timing

let rec spin (n:nat) (acc:int) : Tot int (decreases n) =
  if n = 0 then acc else spin (n - 1) (acc + n)

let work () : ML int = spin 100000 0

let main () : ML FStar.UInt32.t =
  let t1 = T.now_ns () in
  let t2 = T.now_ns () in
  let ok = T.diff_ns t1 t2 >= 0 in
  let ok = T.diff_ms t1 t2 >= 0 && ok in
  let r = T.record_ns work in
  let ok = fst r = 5000050000 && snd r >= 0 && ok in
  let r = T.record_ms work in
  let ok = fst r = 5000050000 && snd r >= 0 && ok in
  let t3 = T.now_ns () in
  let ok = T.diff_ns t1 t3 > 0 && ok in
  if ok then 0ul else 1ul
