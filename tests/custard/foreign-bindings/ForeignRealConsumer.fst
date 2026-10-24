module ForeignRealConsumer
open FStar.All

let main () : ML FStar.Int32.t =
  if FStar.UInt32.eq (Foreign.hook () 2ul) 6ul &&
     FStar.UInt32.eq Foreign.value 6ul
  then 0l else 1l
