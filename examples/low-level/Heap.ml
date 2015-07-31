
type aref =
| Ref of unit * Obj.t ref

let is_Ref = (fun ( _discr_ ) -> (match (_discr_) with
| Ref (_) -> begin
true
end
| _ -> begin
false
end))

let sel = (fun ( _ ) ( _ ) -> (failwith ("Not yet implemented")))

let upd = (fun ( _ ) ( _ ) ( _ ) -> (failwith ("Not yet implemented")))

let emp = (failwith ("Not yet implemented"))

let contains = (fun ( _ ) ( _ ) -> (failwith ("Not yet implemented")))

let equal = (fun ( _ ) ( _ ) -> (failwith ("Not yet implemented")))

let restrict = (fun ( _ ) ( _ ) -> (failwith ("Not yet implemented")))

let concat = (fun ( _ ) ( _ ) -> (failwith ("Not yet implemented")))

type (' r, ' p, ' h) l__On =
' p

type (' refs, ' h0, ' h1) fresh =
(Obj.t ref, (unit Support.Prims.b2t, (unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and) Support.Prims.l_imp) Support.Prims.l__Forall Support.Prims.l__ForallTyp

type (' mods, ' h, ' h') modifies =
unit Support.Prims.b2t

let only = (fun ( x ) -> (Support.Set.singleton (Ref ((), (Obj.magic x)))))

let op_Hat_Plus_Plus = (fun ( r ) ( s ) -> (Support.Set.union (Support.Set.singleton (Ref ((), (Obj.magic r)))) s))

let op_Plus_Plus_Hat = (fun ( s ) ( r ) -> (Support.Set.union s (Support.Set.singleton (Ref ((), (Obj.magic r))))))

let op_Hat_Plus_Hat = (fun ( r1 ) ( r2 ) -> (Support.Set.union (Support.Set.singleton (Ref ((), (Obj.magic r1)))) (Support.Set.singleton (Ref ((), (Obj.magic r2))))))




