open Prims
type 'a thunk = (unit -> 'a, 'a) FStar_Pervasives.either FStar_ST.ref
type 'a t = 'a thunk
let mk : 'a . (unit -> 'a) -> 'a thunk =
  fun f -> FStar_Util.mk_ref (FStar_Pervasives.Inl f)
let mkv : 'a . 'a -> 'a thunk =
  fun v -> FStar_Util.mk_ref (FStar_Pervasives.Inr v)
let force : 'a . 'a thunk -> 'a =
  fun t1 ->
    let uu___ = FStar_ST.op_Bang t1 in
    match uu___ with
    | FStar_Pervasives.Inr a1 -> a1
    | FStar_Pervasives.Inl f ->
        let a1 = f () in
        (FStar_ST.op_Colon_Equals t1 (FStar_Pervasives.Inr a1); a1)
let map : 'a 'b . ('a -> 'b) -> 'a thunk -> 'b thunk =
  fun f -> fun t1 -> mk (fun uu___ -> let uu___1 = force t1 in f uu___1)