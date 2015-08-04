
let withNewScope = (fun ( mods ) ( body ) -> (let _12_35 = (SST.pushStackFrame ())
in (let v = (body ())
in (let _12_38 = (SST.popStackFrame ())
in v))))

let rec scopedWhile = (fun ( wg ) ( mods ) ( bd ) -> (match ((wg ())) with
| true -> begin
(let _12_77 = (withNewScope mods (Obj.magic bd))
in (scopedWhile wg mods bd))
end
| false -> begin
()
end))

let scopedWhile1 = (fun ( r ) ( lc ) ( loopInv ) ( mods ) ( bd ) -> (scopedWhile (Obj.magic (fun ( u ) -> (let _21_6208 = (SST.memread r)
in (lc _21_6208)))) mods bd))




