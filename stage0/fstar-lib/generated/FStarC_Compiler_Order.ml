open Prims
type order =
  | Lt 
  | Eq 
  | Gt 
let (uu___is_Lt : order -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu___ -> false
let (uu___is_Eq : order -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu___ -> false
let (uu___is_Gt : order -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu___ -> false
let (ge : order -> Prims.bool) = fun o -> o <> Lt
let (le : order -> Prims.bool) = fun o -> o <> Gt
let (ne : order -> Prims.bool) = fun o -> o <> Eq
let (gt : order -> Prims.bool) = fun o -> o = Gt
let (lt : order -> Prims.bool) = fun o -> o = Lt
let (eq : order -> Prims.bool) = fun o -> o = Eq
let (lex : order -> (unit -> order) -> order) =
  fun o1 ->
    fun o2 ->
      match (o1, o2) with
      | (Lt, uu___) -> Lt
      | (Eq, uu___) -> o2 ()
      | (Gt, uu___) -> Gt
let (order_from_int : Prims.int -> order) =
  fun i ->
    if i < Prims.int_zero then Lt else if i = Prims.int_zero then Eq else Gt
let (compare_int : Prims.int -> Prims.int -> order) =
  fun i -> fun j -> order_from_int (i - j)
let (compare_bool : Prims.bool -> Prims.bool -> order) =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with
      | (false, true) -> Lt
      | (true, false) -> Gt
      | uu___ -> Eq
let rec compare_list :
  'a . 'a Prims.list -> 'a Prims.list -> ('a -> 'a -> order) -> order =
  fun l1 ->
    fun l2 ->
      fun f ->
        match (l1, l2) with
        | ([], []) -> Eq
        | ([], uu___) -> Lt
        | (uu___, []) -> Gt
        | (x::xs, y::ys) ->
            let uu___ = f x y in
            lex uu___ (fun uu___1 -> compare_list xs ys f)
let compare_option :
  'a .
    ('a -> 'a -> order) ->
      'a FStar_Pervasives_Native.option ->
        'a FStar_Pervasives_Native.option -> order
  =
  fun f ->
    fun x ->
      fun y ->
        match (x, y) with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> Eq
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___)
            -> Lt
        | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None)
            -> Gt
        | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some y1)
            -> f x1 y1