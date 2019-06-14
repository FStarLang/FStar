open Prims
type order =
  | Lt 
  | Eq 
  | Gt 
let (uu___is_Lt : order -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu____8 -> false
let (uu___is_Eq : order -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu____19 -> false
let (uu___is_Gt : order -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu____30 -> false
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
      | (Lt, uu____99) -> Lt
      | (Eq, uu____106) -> o2 ()
      | (Gt, uu____113) -> Gt
let (order_from_int : Prims.int -> order) =
  fun i ->
    if i < (Prims.parse_int "0")
    then Lt
    else if i = (Prims.parse_int "0") then Eq else Gt
let (compare_int : Prims.int -> Prims.int -> order) =
  fun i -> fun j -> order_from_int (i - j)
let rec compare_list :
  'a . ('a -> 'a -> order) -> 'a Prims.list -> 'a Prims.list -> order =
  fun f ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) -> Eq
        | ([], uu____204) -> Lt
        | (uu____211, []) -> Gt
        | (x::xs, y::ys) ->
            let uu____230 = f x y in
            lex uu____230 (fun uu____232 -> compare_list f xs ys)
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
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
           uu____284) -> Lt
        | (FStar_Pervasives_Native.Some uu____289,
           FStar_Pervasives_Native.None) -> Gt
        | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some y1)
            -> f x1 y1