open Prims
let (flip : FStar_Order.order -> FStar_Order.order) =
  fun uu___ ->
    match uu___ with
    | FStar_Order.Lt -> FStar_Order.Gt
    | FStar_Order.Eq -> FStar_Order.Eq
    | FStar_Order.Gt -> FStar_Order.Lt
type 'a raw_comparator = 'a -> 'a -> FStar_Order.order
type 'a totalorder = {
  compare: 'a raw_comparator }
let __proj__Mktotalorder__item__compare :
  'a . 'a totalorder -> 'a raw_comparator =
  fun projectee -> match projectee with | { compare;_} -> compare
let compare : 'a . 'a totalorder -> 'a raw_comparator =
  fun projectee -> match projectee with | { compare = compare1;_} -> compare1
let op_Less : 't . 't totalorder -> 't -> 't -> Prims.bool =
  fun uu___ -> fun x -> fun y -> (compare uu___ x y) = FStar_Order.Lt
let op_Greater : 't . 't totalorder -> 't -> 't -> Prims.bool =
  fun uu___ -> fun x -> fun y -> (compare uu___ x y) = FStar_Order.Gt
let op_Equals : 't . 't totalorder -> 't -> 't -> Prims.bool =
  fun uu___ -> fun x -> fun y -> (compare uu___ x y) = FStar_Order.Eq
let op_Less_Equals : 't . 't totalorder -> 't -> 't -> Prims.bool =
  fun uu___ -> fun x -> fun y -> (compare uu___ x y) <> FStar_Order.Gt
let op_Greater_Equals : 't . 't totalorder -> 't -> 't -> Prims.bool =
  fun uu___ -> fun x -> fun y -> (compare uu___ x y) <> FStar_Order.Lt
let op_Less_Greater : 't . 't totalorder -> 't -> 't -> Prims.bool =
  fun uu___ -> fun x -> fun y -> (compare uu___ x y) <> FStar_Order.Eq
let (uu___0 : Prims.int totalorder) = { compare = FStar_Order.compare_int }
let (uu___1 : Prims.bool totalorder) =
  {
    compare =
      (fun b1 ->
         fun b2 ->
           match (b1, b2) with
           | (false, false) -> FStar_Order.Eq
           | (true, true) -> FStar_Order.Eq
           | (false, uu___) -> FStar_Order.Lt
           | uu___ -> FStar_Order.Gt)
  }
let totalorder_pair :
  'a 'b . 'a totalorder -> 'b totalorder -> ('a * 'b) totalorder =
  fun d1 ->
    fun d2 ->
      {
        compare =
          (fun uu___ ->
             fun uu___2 ->
               match (uu___, uu___2) with
               | ((xa, xb), (ya, yb)) ->
                   (match compare d1 xa ya with
                    | FStar_Order.Lt -> FStar_Order.Lt
                    | FStar_Order.Gt -> FStar_Order.Gt
                    | FStar_Order.Eq -> compare d2 xb yb))
      }
let totalorder_option :
  'a . 'a totalorder -> 'a FStar_Pervasives_Native.option totalorder =
  fun d ->
    {
      compare =
        (fun o1 ->
           fun o2 ->
             match (o1, o2) with
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                 -> FStar_Order.Eq
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
                uu___) -> FStar_Order.Lt
             | (FStar_Pervasives_Native.Some uu___,
                FStar_Pervasives_Native.None) -> FStar_Order.Gt
             | (FStar_Pervasives_Native.Some a1, FStar_Pervasives_Native.Some
                a2) -> compare d a1 a2)
    }
let rec raw_compare_lists :
  'a . 'a totalorder -> 'a Prims.list raw_comparator =
  fun d ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) -> FStar_Order.Eq
        | ([], uu___::uu___2) -> FStar_Order.Lt
        | (uu___::uu___2, []) -> FStar_Order.Gt
        | (x::xs, y::ys) ->
            (match compare d x y with
             | FStar_Order.Lt -> FStar_Order.Lt
             | FStar_Order.Gt -> FStar_Order.Gt
             | FStar_Order.Eq -> raw_compare_lists d xs ys)
let totalorder_list : 'a . 'a totalorder -> 'a Prims.list totalorder =
  fun d -> { compare = (raw_compare_lists d) }