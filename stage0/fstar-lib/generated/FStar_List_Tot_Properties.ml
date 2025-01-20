open Prims
type ('a, 'n) llist = 'a Prims.list
let rec rev' : 'a . 'a Prims.list -> 'a Prims.list =
  fun xs ->
    match xs with
    | [] -> []
    | hd::tl -> FStar_List_Tot_Base.op_At (rev' tl) [hd]
let rev'T : 'uuuuu . unit -> 'uuuuu Prims.list -> 'uuuuu Prims.list =
  fun uu___ -> rev'
let rec sorted : 'a . ('a -> 'a -> Prims.bool) -> 'a Prims.list -> Prims.bool
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> true
      | uu___1::[] -> true
      | x::y::tl -> (f x y) && (sorted f (y :: tl))
type ('a, 'f) total_order = unit