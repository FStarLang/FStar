open Prims
type 'a thunk = (unit -> 'a,'a) FStar_Util.either FStar_ST.ref
type 'a t = 'a thunk
let mk : 'a . (unit -> 'a) -> 'a thunk =
  fun f  -> FStar_Util.mk_ref (FStar_Util.Inl f) 
let mkv : 'a . 'a -> 'a thunk =
  fun v  -> FStar_Util.mk_ref (FStar_Util.Inr v) 
let force : 'a . 'a thunk -> 'a =
  fun t1  ->
    let uu____84 = FStar_ST.op_Bang t1  in
    match uu____84 with
    | FStar_Util.Inr a1 -> a1
    | FStar_Util.Inl f ->
        let a1 = f ()  in
        (FStar_ST.op_Colon_Equals t1 (FStar_Util.Inr a1); a1)
  
let map : 'a 'b . ('a -> 'b) -> 'a thunk -> 'b thunk =
  fun f  ->
    fun t1  ->
      mk (fun uu____208  -> let uu____209 = force t1  in f uu____209)
  