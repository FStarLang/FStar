type 'a heap = ('a ref, 'a) Map.t
type 'a aref = 'a ref
type 'a refs =
  | AllRefs
  | SomeRefs of 'a ref Set.set
let no_refs = SomeRefs Set.empty
let a_ref x = SomeRefs (Set.singleton (ref x))
let sel = Map.sel
let upd = Map.upd
let emp : 'a heap = BatMap.empty
let contains h k = BatMap.mem k h
let equal = Map.equal
let restrict h dom = BatMap.filter (fun k v -> Set.mem k dom) h
let concat  = Map.concat
