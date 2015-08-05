
let withNewScope = (fun ( mods ) ( body ) -> (let _12_35 = (SST.pushStackFrame ())
in (let v = (body ())
in (let _12_38 = (SST.popStackFrame ())
in v))))

let rec scopedWhile = (fun ( wg ) ( mods ) ( bd ) -> (match ((wg ())) with
| true -> begin
(let _12_77 = (withNewScope () (Obj.magic bd))
in (scopedWhile wg () bd))
end
| false -> begin
()
end))

let scopedWhile1 = (fun ( r ) ( lc ) ( loopInv ) ( mods ) ( bd ) -> (scopedWhile (Obj.magic (fun ( u ) -> (let _13_3745 = (SST.memread r)
in (lc _13_3745)))) () bd))

let scopedWhile2 = (fun ( ra ) ( rb ) ( lc ) ( loopInv ) ( mods ) ( bd ) -> (scopedWhile (Obj.magic (fun ( u ) -> (let _13_3783 = (SST.memread ra)
in (let _13_3782 = (SST.memread rb)
in (lc _13_3783 _13_3782))))) () bd))




