module ForeignStubConsumer
open FStar.All

let main () : ML FStar.Int32.t =
  if FStar.UInt32.eq (FStar.Stubs.ForeignBinding.hook () 2ul) 5ul
  then 0l else 1l
