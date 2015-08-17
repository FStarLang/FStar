
type point =
{x : int; y : int}


let lx = (fun ( p ) -> (SST.llift (fun ( p ) -> p.x) p))

let lallocExample1 = (fun ( p ) -> (let _15_15 = (SST.pushStackFrame ())
(* in (let sp = (SST.lalloc p) this line was manually replaced by the line below*)
in (let sp = (Obj.magic (Camlstack.mkpair p.x p.y))	
in (let r = (lx sp)
in (let _15_19 = (SST.popStackFrame ())
in (r + 1))))))




