open Fstarcompiler
open Prims
type 'n swap = Prims.nat
let rec apply_swap_aux :
  'a . Prims.nat -> 'a Prims.list -> Obj.t swap -> 'a Prims.list =
  fun n xs s ->
    match xs with
    | [] -> xs
    | uu___::[] -> xs
    | x1::x2::xs' ->
        if n = s
        then x2 :: x1 :: xs'
        else x1 :: (apply_swap_aux (n + Prims.int_one) (x2 :: xs') s)
let apply_swap (uu___ : unit) : 'a Prims.list -> Obj.t swap -> 'a Prims.list=
  apply_swap_aux Prims.int_zero
let rec apply_swaps :
  'a . 'a Prims.list -> Obj.t swap Prims.list -> 'a Prims.list =
  fun xs ss ->
    match ss with
    | [] -> xs
    | s::ss' -> apply_swaps ((apply_swap ()) xs s) ss'
type ('a, 'xs, 'ys) equal_counts = unit
type ('a, 'xs) swap_for = Obj.t swap
type ('a, 'xs) swaps_for = Obj.t swap Prims.list
let rec lift_swaps_cons :
  'a . 'a -> 'a Prims.list -> Obj.t swap Prims.list -> Obj.t swap Prims.list
  =
  fun h xs ss ->
    match ss with
    | [] -> []
    | s::st -> (s + Prims.int_one) ::
        (lift_swaps_cons h ((apply_swap ()) xs s) st)
let rec swap_to_front : 'a . 'a -> 'a Prims.list -> Obj.t swap Prims.list =
  fun h xs ->
    match xs with
    | [] -> []
    | x::xt ->
        if x = h
        then []
        else
          (let ss = swap_to_front h xt in
           let ss' = lift_swaps_cons x xt ss in
           let s = Prims.int_zero in FStar_List_Tot_Base.op_At ss' [s])
let rec equal_counts_implies_swaps :
  'a . 'a Prims.list -> 'a Prims.list -> Obj.t swap Prims.list =
  fun xs ys ->
    match ys with
    | [] -> (match xs with | [] -> [] | x::xt -> [])
    | y::yt ->
        let ss0 = swap_to_front y xs in
        let xs' = apply_swaps xs ss0 in
        let xt = FStar_List_Tot_Base.tl xs' in
        let ss1 = equal_counts_implies_swaps xt yt in
        let ss1' = lift_swaps_cons y xt ss1 in
        FStar_List_Tot_Base.op_At ss0 ss1'
