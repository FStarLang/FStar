
type sizedListNonGhost =
| MkSListNG of (*Prims.nat*) int * int list

let is_MkSListNG = (fun ( _discr_ ) -> (match (_discr_) with
| MkSListNG (_) -> begin
true
end
| _ -> begin
false
end))

let aSizedListNG = MkSListNG (2, (1)::[])

type sizedList =
| MkSList of unit * int list

let is_MkSList = (fun ( _discr_ ) -> (match (_discr_) with
| MkSList (_) -> begin
true
end
| _ -> begin
false
end))

let aSizedList = (fun ( u ) -> (let h2 = ()
in MkSList ((), (1)::[])))




