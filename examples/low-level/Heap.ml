
type aref =
| Ref of unit * Obj.t Prims.ref

let is_Ref = (fun ( _discr_ ) -> (match (_discr_) with
| Ref (_) -> begin
true
end
| _ -> begin
false
end))



let sel = (fun ( _7_16450  :  unit ) -> (failwith () "Not yet implemented"))

let upd = (fun ( _7_16450  :  unit ) -> (failwith () "Not yet implemented"))

let emp = (failwith () "Not yet implemented")

let contains = (fun ( _7_16450  :  unit ) -> (failwith () "Not yet implemented"))

let equal = (failwith () "Not yet implemented")

let restrict = (failwith () "Not yet implemented")

let concat = (failwith () "Not yet implemented")

type ('r, 'p, 'h) On =
'p

type ('refs, 'h0, 'h1) fresh =
(Obj.t Prims.ref, (unit Prims.b2t, (unit Prims.b2t, unit Prims.b2t) Prims.l_and) Prims.l_imp) Prims.l__Forall Prims.l__ForallTyp

type ('mods, 'h, 'h') modifies =
unit Prims.b2t

let only = (fun ( _7_16450  :  unit ) -> (fun ( x  :  '_3_1078 Prims.ref ) -> (Set.singleton () (Ref ((), (Obj.magic x))))))

let op_Hat_Plus_Plus = (fun ( _7_16450  :  unit ) ( r  :  'a Prims.ref ) ( s  :  aref Set.set ) -> (Set.union () (Set.singleton () (Ref ((), (Obj.magic r)))) s))

let op_Plus_Plus_Hat = (fun ( _7_16450  :  unit ) ( s  :  aref Set.set ) ( r  :  'a Prims.ref ) -> (Set.union () s (Set.singleton () (Ref ((), (Obj.magic r))))))

let op_Hat_Plus_Hat = (fun ( _7_16450  :  unit ) ( r1  :  'a Prims.ref ) ( r2  :  'b Prims.ref ) -> (Set.union () (Set.singleton () (Ref ((), (Obj.magic r1)))) (Set.singleton () (Ref ((), (Obj.magic r2))))))




