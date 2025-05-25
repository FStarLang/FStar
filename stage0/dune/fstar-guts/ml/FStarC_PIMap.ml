module ZMap = BatMap.Make(Z)

type 'value t = 'value ZMap.t
let empty (_: unit) : 'value t = ZMap.empty
let add (map: 'value t) (key: Z.t) (value: 'value) = ZMap.add key value map
let find_default (map: 'value t) (key: Z.t) (dflt: 'value) =
  ZMap.find_default dflt key map
let try_find (map: 'value t) (key: Z.t) =
  ZMap.Exceptionless.find key map
let fold (m:'value t) f a = ZMap.fold f m a
let remove (m:'value t) k = ZMap.remove k m

type 'value pimap = 'value t
let pimap_empty = empty
let pimap_add = add
let pimap_find_default = find_default
let pimap_try_find = try_find
let pimap_fold = fold
let pimap_remove = remove
