
open Prims
type ' a cmp =
' a  ->  ' a  ->  Prims.bool

type (' k, ' v, ' f, ' d) map_t =
' k  ->  ' v Prims.option

type ('dummyV3, 'dummyV2, 'dummyV1) ordmap =
| Mk_map of Prims.unit * Prims.unit * Obj.t cmp * (Obj.t, Prims.unit) FStar_OrdSet.ordset * (Obj.t, Obj.t, Prims.unit, Prims.unit) map_t

let is_Mk_map = (fun _discr_ -> (match (_discr_) with
| Mk_map (_) -> begin
true
end
| _ -> begin
false
end))

let ___Mk_map___f = (fun _2 projectee -> (match (projectee) with
| Mk_map (_, _, _13_26, _13_29, _13_30) -> begin
(Obj.magic _13_26)
end))

let ___Mk_map___d = (fun _2 projectee -> (match (projectee) with
| Mk_map (_, _, _13_34, _13_31, _13_35) -> begin
(Obj.magic _13_31)
end))

let ___Mk_map___m = (fun _2 projectee -> (match (projectee) with
| Mk_map (_, _, _13_39, _13_40, _13_36) -> begin
(Obj.magic _13_36)
end))

let empty = (Obj.magic (fun f -> (let d = (FStar_OrdSet.empty (Obj.magic ((fun k v f -> ((fun k v f -> f) () () f)) () () (Obj.magic f))))
in (let g = (fun x -> None)
in Mk_map ((), (), ((fun k v f d g -> ((fun k v f -> f) () () f)) () () (Obj.magic f) (Obj.magic d) (Obj.magic g)), (Obj.magic d), (Obj.magic g))))))

let const_on = (Obj.magic (fun f d x -> (let g = (fun y -> if (FStar_OrdSet.mem (Obj.magic ((fun k v f d x y -> f) () () (Obj.magic f) (Obj.magic d) (Obj.magic x) (Obj.magic y))) y d) then begin
Some (x)
end else begin
None
end)
in Mk_map ((), (), ((fun k v f d x g -> f) () () (Obj.magic f) (Obj.magic d) (Obj.magic x) (Obj.magic g)), (Obj.magic d), (Obj.magic g)))))

let select = (Obj.magic (fun f x m -> (___Mk_map___m (Obj.magic ((fun k v f x m -> f) () () (Obj.magic f) (Obj.magic x) (Obj.magic m))) m (Obj.magic x))))

let insert = (fun f x s -> (FStar_OrdSet.union f (FStar_OrdSet.singleton f x) s))

let update = (Obj.magic (fun f x y m -> (let s' = (insert (Obj.magic ((fun k v f x y m -> (___Mk_map___f ((fun k v f x y m -> f) () () f x y m) m)) () () (Obj.magic f) (Obj.magic x) (Obj.magic y) (Obj.magic m))) (Obj.magic x) (___Mk_map___d (Obj.magic ((fun k v f x y m -> f) () () (Obj.magic f) (Obj.magic x) (Obj.magic y) (Obj.magic m))) m))
in (let g' = (fun x' -> if (x' = (Obj.magic x)) then begin
Some ((Obj.magic y))
end else begin
(___Mk_map___m (Obj.magic ((fun k v f x y m s' x' -> f) () () (Obj.magic f) (Obj.magic x) (Obj.magic y) (Obj.magic m) (Obj.magic s') (Obj.magic x'))) m x')
end)
in Mk_map ((), (), (Obj.magic ((fun k v f x y m s' g' -> ((fun k v f x y m -> (___Mk_map___f ((fun k v f x y m -> f) () () f x y m) m)) () () f x y m)) () () (Obj.magic f) (Obj.magic x) (Obj.magic y) (Obj.magic m) (Obj.magic s') (Obj.magic g'))), (Obj.magic s'), (Obj.magic g'))))))

let contains = (fun f x m -> (FStar_OrdSet.mem (Obj.magic ((fun k v f x m -> (___Mk_map___f ((fun k v f x m -> f) () () f x m) m)) () () (Obj.magic f) (Obj.magic x) (Obj.magic m))) (Obj.magic x) (___Mk_map___d (Obj.magic ((fun k v f x m -> f) () () (Obj.magic f) (Obj.magic x) (Obj.magic m))) m)))

let dom = (Obj.magic (fun f m -> (___Mk_map___d (Obj.magic ((fun k v f m -> f) () () (Obj.magic f) (Obj.magic m))) m)))

let remove = (Obj.magic (fun f x m -> (let s' = (FStar_OrdSet.remove (Obj.magic ((fun k v f x m -> (___Mk_map___f ((fun k v f x m -> f) () () f x m) m)) () () (Obj.magic f) (Obj.magic x) (Obj.magic m))) (Obj.magic x) (___Mk_map___d (Obj.magic ((fun k v f x m -> f) () () (Obj.magic f) (Obj.magic x) (Obj.magic m))) m))
in (let g' = (fun x' -> if (x' = (Obj.magic x)) then begin
None
end else begin
(___Mk_map___m (Obj.magic ((fun k v f x m s' x' -> f) () () (Obj.magic f) (Obj.magic x) (Obj.magic m) (Obj.magic s') (Obj.magic x'))) m x')
end)
in Mk_map ((), (), (Obj.magic ((fun k v f x m s' g' -> ((fun k v f x m -> (___Mk_map___f ((fun k v f x m -> f) () () f x m) m)) () () f x m)) () () (Obj.magic f) (Obj.magic x) (Obj.magic m) (Obj.magic s') (Obj.magic g'))), (Obj.magic s'), (Obj.magic g'))))))

let choose = (fun f m -> (match ((FStar_OrdSet.choose (Obj.magic ((fun k v f m -> (___Mk_map___f ((fun k v f m -> f) () () f m) m)) () () (Obj.magic f) (Obj.magic m))) (___Mk_map___d (Obj.magic ((fun k v f m -> f) () () (Obj.magic f) (Obj.magic m))) m))) with
| None -> begin
None
end
| Some (x) -> begin
Some (((Obj.magic x), (Obj.magic (Prims.___Some___v (___Mk_map___m (Obj.magic ((fun k v f m x -> f) () () (Obj.magic f) (Obj.magic m) (Obj.magic x))) m x)))))
end))

let size = (fun f m -> (FStar_OrdSet.size (Obj.magic ((fun k v f m -> (___Mk_map___f ((fun k v f m -> f) () () f m) m)) () () (Obj.magic f) (Obj.magic m))) (___Mk_map___d (Obj.magic ((fun k v f m -> f) () () (Obj.magic f) (Obj.magic m))) m)))

let eq_intro = (fun f m1 m2 -> ())

let eq_lemma = (fun f m1 m2 -> ())

let upd_order = (fun f x y x' y' m -> ())

let upd_same_k = (fun f x y y' m -> ())

let sel_upd1 = (fun f x y m -> ())

let sel_upd2 = (fun f x y x' m -> ())

let sel_empty = (fun f x -> ())

let sel_contains = (fun f x m -> ())

let contains_upd1 = (fun f x y x' m -> ())

let contains_upd2 = (fun f x y x' m -> ())

let contains_empty = (fun f x -> ())

let contains_remove = (fun f x y m -> ())

let eq_remove = (fun f x m -> ())

let choose_empty = (fun f -> ())

let dom_empty_helper = (fun f m -> ())

let choose_m = (fun f m -> ())

let size_empty = (fun f -> ())

let size_remove = (fun f y m -> ())

let dom_lemma = (fun f x m -> ())

let contains_const_on = (fun f d x y -> ())

let select_const_on = (fun f d x y -> ())

let sel_rem1 = (fun f x m -> ())

let sel_rem2 = (fun f x x' m -> ())

let rem_upd = (fun f x y x' m -> ())




