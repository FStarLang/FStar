module ForeignNamingConsumer
open FStar.All

let main () : ML FStar.Int32.t =
  if FStar.UInt32.eq (Foreign.other 1ul) 1ul &&
     FStar.UInt32.eq (ForeignAlias.hook 1ul) 2ul &&
     FStar.UInt32.eq (Foreign.hook () 2ul) 5ul
  then 0l else 1l
