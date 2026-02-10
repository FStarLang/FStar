open Prims
type 'a path = 'a Prims.list
type ('a, 'qual) forest = (('a path * 'qual) Prims.list * 'qual)
let rec is_under :
  'a . 'a FStarC_Class_Deq.deq -> 'a path -> 'a path -> Prims.bool =
  fun uu___ p1 p2 ->
    match (p1, p2) with
    | (uu___1, []) -> true
    | ([], uu___1) -> false
    | (h1::t1, h2::t2) ->
        (FStarC_Class_Deq.op_Equals_Question uu___ h1 h2) &&
          (is_under uu___ t1 t2)
let search_forest (uu___ : 'a FStarC_Class_Deq.deq) (p : 'a path)
  (f : ('a, 'q) forest) : 'q=
  let uu___1 = f in
  match uu___1 with
  | (roots, def) ->
      let rec aux roots1 =
        match roots1 with
        | [] -> def
        | (r, q1)::rs ->
            let uu___2 = is_under uu___ p r in if uu___2 then q1 else aux rs in
      aux roots
