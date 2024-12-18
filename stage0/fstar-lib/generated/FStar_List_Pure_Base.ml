open Prims
let rec map2 :
  'a1 'a2 'b .
    ('a1 -> 'a2 -> 'b) -> 'a1 Prims.list -> 'a2 Prims.list -> 'b Prims.list
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) -> []
        | (x1::xs1, x2::xs2) -> (f x1 x2) :: (map2 f xs1 xs2)
let rec map3 :
  'a1 'a2 'a3 'b .
    ('a1 -> 'a2 -> 'a3 -> 'b) ->
      'a1 Prims.list -> 'a2 Prims.list -> 'a3 Prims.list -> 'b Prims.list
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        fun l3 ->
          match (l1, l2, l3) with
          | ([], [], []) -> []
          | (x1::xs1, x2::xs2, x3::xs3) -> (f x1 x2 x3) ::
              (map3 f xs1 xs2 xs3)
let zip :
  'a1 'a2 . 'a1 Prims.list -> 'a2 Prims.list -> ('a1 * 'a2) Prims.list =
  fun l1 -> fun l2 -> map2 (fun x -> fun y -> (x, y)) l1 l2
let zip3 :
  'a1 'a2 'a3 .
    'a1 Prims.list ->
      'a2 Prims.list -> 'a3 Prims.list -> ('a1 * 'a2 * 'a3) Prims.list
  =
  fun l1 ->
    fun l2 -> fun l3 -> map3 (fun x -> fun y -> fun z -> (x, y, z)) l1 l2 l3