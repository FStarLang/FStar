
let withNewScope = (fun ( mods ) ( body ) -> (let _10_35 = (SST.pushStackFrame ())
in (let v = (body ())
in (let _10_38 = (SST.popStackFrame ())
in v))))

let rec scopedWhile = (fun ( wg ) ( mods ) ( bd ) -> (match ((wg ())) with
| true -> begin
(let _10_77 = (withNewScope mods (Obj.magic bd))
in (scopedWhile wg mods bd))
end
| false -> begin
()
end))

let scopedWhile1 = (fun ( r ) ( lc ) ( loopInv ) ( mods ) ( bd ) -> (scopedWhile (Obj.magic (fun ( u ) -> (let _10_4195 = (SST.memread r)
in (lc _10_4195)))) mods bd))




