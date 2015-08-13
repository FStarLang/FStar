
type ' a lref =
' a Support.ST.ref Located.located

type heap =
unit

type aref =
| Ref of unit * Obj.t lref

let is_Ref = (fun ( _discr_ ) -> (match (_discr_) with
| Ref (_) -> begin
true
end
| _ -> begin
false
end))

let ___Ref___r = (fun ( projectee ) -> (match (projectee) with
| Ref (_, _12_5) -> begin
(Obj.magic _12_5)
end))

let sel = (fun ( _ ) ( _ ) -> (Support.All.failwith "Not yet implemented:sel"))

let upd = (fun ( _ ) ( _ ) ( _ ) -> (Support.All.failwith "Not yet implemented:upd"))

let emp = () (*this line was manually edited, everything else is as extracted*)

let contains = (fun ( _ ) ( _ ) -> (Support.All.failwith "Not yet implemented:contains"))

let equal = (fun ( _ ) ( _ ) -> (Support.All.failwith "Not yet implemented:equal"))

let restrict = (fun ( _ ) ( _ ) -> (Support.All.failwith "Not yet implemented:restrict"))

let concat = (fun ( _ ) ( _ ) -> (Support.All.failwith "Not yet implemented:concat"))

type (' r, ' p, ' h) l__On =
' p

type (' lrefs, ' h0, ' h1) fresh =
(Obj.t lref, (unit Support.Prims.b2t, (unit Support.Prims.b2t, unit Support.Prims.b2t) Support.Prims.l_and) Support.Prims.l_imp) Support.Prims.l__Forall Support.Prims.l__ForallTyp

type (' mods, ' h, ' h') modifies =
unit Support.Prims.b2t

type modset =
unit

let only = (fun ( x ) -> ())

let eonly = (fun ( r ) -> ())

let eunion = (fun ( s1 ) ( s2 ) -> ())

let eunionUnion = (fun ( r1 ) ( r2 ) -> ())




