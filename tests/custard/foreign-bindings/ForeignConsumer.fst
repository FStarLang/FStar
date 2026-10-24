module ForeignConsumer
open FStar.All

let main () : ML FStar.Int32.t =
  if FStar.UInt32.eq (ForeignProducer.api 1ul) 9ul &&
     FStar.UInt32.eq (Foreign.hook () 2ul) 5ul &&
     FStar.UInt32.eq Foreign.value 5ul &&
     FStar.UInt32.eq (Foreign.identity 7ul) 7ul &&
     FStar.UInt64.eq (Foreign.identity 9UL) 9UL
  then 0l else 1l
