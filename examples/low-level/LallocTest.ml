
type point =
{x : int; y : int}

let is_Mkpoint = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:LallocTest.is_Mkpoint"))

let lx = (fun ( p ) -> (SST.llift (fun ( p ) -> p.x) p))

let lallocExample1 = (fun ( px ) ( py ) -> (let _15_17 = (SST.pushStackFrame ())
in (let sp = (Obj.magic (Camlstack.mkpair px py))
in (let r = (lx sp)
in (let _15_21 = (SST.popStackFrame ())
in (r + 1))))))




