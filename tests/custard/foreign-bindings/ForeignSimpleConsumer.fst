module ForeignSimpleConsumer
open FStar.All

let main () : ML FStar.Int32.t =
  if FStar.UInt32.eq (Foreign.hook () 2ul) 5ul &&
     FStar.UInt32.eq Foreign.value 5ul
  then 0l else 1l
