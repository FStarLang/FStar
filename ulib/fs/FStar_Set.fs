module FStar_Set

type set<'a when 'a : comparison> = Set<'a>
let empty () = Set.empty
let singleton = Set.singleton
let union = Set.union
let intersect = Set.intersect
let complement x = Set.empty // TODO
let mem = Set.contains

(*
 * F* should not extract Set.equal
 * We should fix it, adding the following in the meantime
 *)
type equal = unit
