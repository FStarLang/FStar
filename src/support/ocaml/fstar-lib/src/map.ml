type ('a, 'b) t =  ('a, 'b) BatMap.t
let sel m k = BatMap.find k m
let upd m k v = BatMap.add k v m
let const x = BatMap.empty
let concat = BatMap.union
let equal x y =
  (BatMap.is_empty x && BatMap.is_empty y) || (BatMap.is_empty (BatMap.filter (fun k v -> try BatMap.find k x<>v with Not_found -> true) y))

