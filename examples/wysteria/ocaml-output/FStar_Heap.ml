
open Prims
type aref =
| Ref of Prims.unit * Obj.t ref

let is_Ref = (fun _discr_ -> (match (_discr_) with
| Ref (_) -> begin
true
end
| _ -> begin
false
end))

let ___Ref___r = (fun projectee -> (match (projectee) with
| Ref (_, _5_4) -> begin
(Obj.magic _5_4)
end))

let sel = (Obj.magic (fun _ _ -> (FStar_All.failwith "Not yet implemented:sel")))

let upd = (Obj.magic (fun _ _ _ -> (FStar_All.failwith "Not yet implemented:upd")))

let emp = (FStar_All.failwith "Not yet implemented:emp")

let contains = (Obj.magic (fun _ _ -> (FStar_All.failwith "Not yet implemented:contains")))

let equal = (Obj.magic (fun _ _ -> (FStar_All.failwith "Not yet implemented:equal")))

let restrict = (Obj.magic (fun _ _ -> (FStar_All.failwith "Not yet implemented:restrict")))

let concat = (Obj.magic (fun _ _ -> (FStar_All.failwith "Not yet implemented:concat")))

type (' r, ' p, ' h) l__On =
' p

let only = (fun x -> (FStar_Set.singleton (Ref ((), (Obj.magic x)))))

let op_Hat_Plus_Plus = (fun r s -> (FStar_Set.union (FStar_Set.singleton (Ref ((), (Obj.magic r)))) s))

let op_Plus_Plus_Hat = (fun s r -> (FStar_Set.union s (FStar_Set.singleton (Ref ((), (Obj.magic r))))))

let op_Hat_Plus_Hat = (fun r1 r2 -> (FStar_Set.union (FStar_Set.singleton (Ref ((), (Obj.magic r1)))) (FStar_Set.singleton (Ref ((), (Obj.magic r2))))))




