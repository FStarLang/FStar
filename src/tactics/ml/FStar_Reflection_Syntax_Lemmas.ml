open Prims
let uncurry:
  'a 'b 'c . ('a -> 'b -> 'c) -> ('a,'b) FStar_Pervasives_Native.tuple2 -> 'c
  = fun f  -> fun uu____39  -> match uu____39 with | (x,y) -> f x y
let curry:
  'a 'b 'c . (('a,'b) FStar_Pervasives_Native.tuple2 -> 'c) -> 'a -> 'b -> 'c
  = fun f  -> fun x  -> fun y  -> f (x, y)
let rec mk_app_collect_inv_s:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list -> Prims.unit
  = fun t  -> fun args  -> ()
let rec mk_app_collect_inv: FStar_Reflection_Types.term -> Prims.unit =
  fun t  -> ()
let rec forall_list: 'a 'Ap . 'a Prims.list -> Obj.t =
  fun a266  -> (Obj.magic (fun l  -> ())) a266
let rec collect_app_order':
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term -> Prims.unit
  = fun args  -> fun tt  -> fun t  -> ()
let collect_app_order: FStar_Reflection_Types.term -> Prims.unit =
  fun t  -> ()
let rec list_ref: 'Aa 'Ap . 'Aa Prims.list -> 'Aa Prims.list =
  fun l  -> match l with | [] -> [] | x::xs -> x :: (list_ref xs)
let collect_app_ref:
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term,FStar_Reflection_Types.term Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match FStar_Reflection_Syntax.collect_app t with
    | (h,a) -> (h, (list_ref a))