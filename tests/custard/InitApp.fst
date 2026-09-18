module InitApp
module I32 = FStar.Int32
open FStar.All

let main () : ML I32.t =
  if InitMiddle.read () = 7ul then 0l else 1l
