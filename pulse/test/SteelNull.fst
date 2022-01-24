module SteelNull

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let r = null #UInt32.t in
  if is_null r then
    return 0l
  else
    return 1l
