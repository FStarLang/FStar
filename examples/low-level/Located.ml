
type 't located = 't (*this line and the definitions of locate and unlocate were manually added,
 everything else is as extracted*)

type sidt =
Support.Prims.nat

type regionLoc =
| InHeap
| InStack of sidt

let is_InHeap = (fun ( _discr_ ) -> (match (_discr_) with
| InHeap -> begin
true
end
| _ -> begin
false
end))

let is_InStack = (fun ( _discr_ ) -> (match (_discr_) with
| InStack (_) -> begin
true
end
| _ -> begin
false
end))

let ___InStack___id = (fun ( projectee ) -> (match (projectee) with
| InStack (_11_4) -> begin
_11_4
end))

let regionOf = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:regionOf"))


let locate = (fun ( x ) -> x)

let unlocate = (fun ( l ) -> l)




