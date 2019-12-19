open Prims
type 'a thunk = (unit -> 'a,'a) FStar_Util.either FStar_ST.ref
type 'a t = 'a thunk
let mk : 'a . (unit -> 'a) -> 'a thunk =
  fun f  -> FStar_Util.mk_ref (FStar_Util.Inl f) 
let mkv : 'a . 'a -> 'a thunk =
  fun v1  -> FStar_Util.mk_ref (FStar_Util.Inr v1) 
let force : 'a . 'a thunk -> 'a =
  fun t  ->
    let uu____84 = FStar_ST.op_Bang t  in
    match uu____84 with
    | FStar_Util.Inr a -> a
    | FStar_Util.Inl f ->
        let a = f ()  in (FStar_ST.op_Colon_Equals t (FStar_Util.Inr a); a)
  
let map : 'a 'b . ('a -> 'b) -> 'a thunk -> 'b thunk =
  fun f  ->
    fun t  -> mk (fun uu____208  -> let uu____209 = force t  in f uu____209)
  