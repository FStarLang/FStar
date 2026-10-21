module CIfDefApp

open FStar.All
module I32 = FStar.Int32

let main () : ML I32.t =
  let result = CIfDef.main () in
  if CIfDef.second then (if I32.eq result 0l then 0l else 2l) else result
