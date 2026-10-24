module CherryTime

(* FStarC.Time-c.cherry.fst: the wall clock, file modification times, and
   the rendering of a time as seconds and microseconds. *)
open FStarC.Effect
open FStarC.Class.Show
module T = FStarC.Time

let main () : ML FStar.UInt32.t =
  let t1 = T.get_time_of_day () in
  let t2 = T.get_time_of_day () in
  let ok = not (T.is_before t2 t1) in
  (* After 2020-01-01. *)
  let ok = T.get_time_of_day_ms () > 1577836800000 && ok in
  let m = T.get_file_last_modification_time "." in
  let ok = not (T.is_before t2 m) && T.is_before (T.get_file_last_modification_time "/") t2 && ok in
  let ok = (try let _ = T.get_file_last_modification_time "no/such/file" in false
            with | _ -> true) && ok in
  (* Ten digits of seconds until 2286, a point and six of microseconds. *)
  let s = show t1 in
  let ok = FStar.String.length s = 17 && FStar.String.index s 10 = '.' && ok in
  if ok then 0ul else 1ul
