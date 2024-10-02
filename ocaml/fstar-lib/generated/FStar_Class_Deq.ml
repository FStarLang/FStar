open Prims
type 'a deq = {
  op_Equals_Question: 'a -> 'a -> Prims.bool }
let __proj__Mkdeq__item__op_Equals_Question :
  'a . 'a deq -> 'a -> 'a -> Prims.bool =
  fun projectee ->
    match projectee with | { op_Equals_Question;_} -> op_Equals_Question
let op_Equals_Question : 'a . 'a deq -> 'a -> 'a -> Prims.bool =
  fun projectee ->
    match projectee with
    | { op_Equals_Question = op_Equals_Question1;_} -> op_Equals_Question1
let op_Less_Greater_Question : 'a . 'a deq -> 'a -> 'a -> Prims.bool =
  fun uu___ ->
    fun x ->
      fun y ->
        let uu___1 = op_Equals_Question uu___ x y in Prims.op_Negation uu___1
let (deq_int : Prims.int deq) =
  { op_Equals_Question = (fun x -> fun y -> x = y) }
let (deq_bool : Prims.bool deq) =
  { op_Equals_Question = (fun x -> fun y -> x = y) }
let (deq_unit : unit deq) = { op_Equals_Question = (fun x -> fun y -> true) }
let (deq_string : Prims.string deq) =
  { op_Equals_Question = (fun x -> fun y -> x = y) }
let deq_option : 'a . 'a deq -> 'a FStar_Pervasives_Native.option deq =
  fun uu___ ->
    {
      op_Equals_Question =
        (fun x ->
           fun y ->
             match (x, y) with
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                 -> true
             | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some
                y1) -> op_Equals_Question uu___ x1 y1
             | (uu___1, uu___2) -> false)
    }
let rec eqList : 'a . 'a deq -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq ->
    fun xs ->
      fun ys ->
        match (xs, ys) with
        | ([], []) -> true
        | (x::xs1, y::ys1) ->
            (op_Equals_Question eq x y) && (eqList eq xs1 ys1)
        | (uu___, uu___1) -> false
let deq_list : 'a . 'a deq -> 'a Prims.list deq =
  fun d -> { op_Equals_Question = (eqList d) }
let deq_either :
  'a 'b . 'a deq -> 'b deq -> ('a, 'b) FStar_Pervasives.either deq =
  fun d1 ->
    fun d2 ->
      {
        op_Equals_Question =
          (fun x ->
             fun y ->
               match (x, y) with
               | (FStar_Pervasives.Inl x1, FStar_Pervasives.Inl y1) ->
                   op_Equals_Question d1 x1 y1
               | (FStar_Pervasives.Inr x1, FStar_Pervasives.Inr y1) ->
                   op_Equals_Question d2 x1 y1
               | (uu___, uu___1) -> false)
      }
let deq_tuple2 : 'a 'b . 'a deq -> 'b deq -> ('a * 'b) deq =
  fun d1 ->
    fun d2 ->
      {
        op_Equals_Question =
          (fun uu___ ->
             fun uu___1 ->
               match (uu___, uu___1) with
               | ((x1, x2), (y1, y2)) ->
                   (op_Equals_Question d1 x1 y1) &&
                     (op_Equals_Question d2 x2 y2))
      }
let deq_tuple3 : 'a 'b 'c . 'a deq -> 'b deq -> 'c deq -> ('a * 'b * 'c) deq
  =
  fun d1 ->
    fun d2 ->
      fun d3 ->
        {
          op_Equals_Question =
            (fun uu___ ->
               fun uu___1 ->
                 match (uu___, uu___1) with
                 | ((x1, x2, x3), (y1, y2, y3)) ->
                     ((op_Equals_Question d1 x1 y1) &&
                        (op_Equals_Question d2 x2 y2))
                       && (op_Equals_Question d3 x3 y3))
        }
let deq_tuple4 :
  'a 'b 'c 'd .
    'a deq -> 'b deq -> 'c deq -> 'd deq -> ('a * 'b * 'c * 'd) deq
  =
  fun d1 ->
    fun d2 ->
      fun d3 ->
        fun d4 ->
          {
            op_Equals_Question =
              (fun uu___ ->
                 fun uu___1 ->
                   match (uu___, uu___1) with
                   | ((x1, x2, x3, x4), (y1, y2, y3, y4)) ->
                       (((op_Equals_Question d1 x1 y1) &&
                           (op_Equals_Question d2 x2 y2))
                          && (op_Equals_Question d3 x3 y3))
                         && (op_Equals_Question d4 x4 y4))
          }
let deq_tuple5 :
  'a 'b 'c 'd 'e .
    'a deq ->
      'b deq -> 'c deq -> 'd deq -> 'e deq -> ('a * 'b * 'c * 'd * 'e) deq
  =
  fun d1 ->
    fun d2 ->
      fun d3 ->
        fun d4 ->
          fun d5 ->
            {
              op_Equals_Question =
                (fun uu___ ->
                   fun uu___1 ->
                     match (uu___, uu___1) with
                     | ((x1, x2, x3, x4, x5), (y1, y2, y3, y4, y5)) ->
                         ((((op_Equals_Question d1 x1 y1) &&
                              (op_Equals_Question d2 x2 y2))
                             && (op_Equals_Question d3 x3 y3))
                            && (op_Equals_Question d4 x4 y4))
                           && (op_Equals_Question d5 x5 y5))
            }
let deq_tuple6 :
  'a 'b 'c 'd 'e 'f .
    'a deq ->
      'b deq ->
        'c deq ->
          'd deq -> 'e deq -> 'f deq -> ('a * 'b * 'c * 'd * 'e * 'f) deq
  =
  fun d1 ->
    fun d2 ->
      fun d3 ->
        fun d4 ->
          fun d5 ->
            fun d6 ->
              {
                op_Equals_Question =
                  (fun uu___ ->
                     fun uu___1 ->
                       match (uu___, uu___1) with
                       | ((x1, x2, x3, x4, x5, x6), (y1, y2, y3, y4, y5, y6))
                           ->
                           (((((op_Equals_Question d1 x1 y1) &&
                                 (op_Equals_Question d2 x2 y2))
                                && (op_Equals_Question d3 x3 y3))
                               && (op_Equals_Question d4 x4 y4))
                              && (op_Equals_Question d5 x5 y5))
                             && (op_Equals_Question d6 x6 y6))
              }