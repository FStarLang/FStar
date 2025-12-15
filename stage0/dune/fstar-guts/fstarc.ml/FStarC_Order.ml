open Prims
type order =
  | Lt 
  | Eq 
  | Gt 
let uu___is_Lt (projectee : order) : Prims.bool=
  match projectee with | Lt -> true | uu___ -> false
let uu___is_Eq (projectee : order) : Prims.bool=
  match projectee with | Eq -> true | uu___ -> false
let uu___is_Gt (projectee : order) : Prims.bool=
  match projectee with | Gt -> true | uu___ -> false
let ge (o : order) : Prims.bool= o <> Lt
let le (o : order) : Prims.bool= o <> Gt
let ne (o : order) : Prims.bool= o <> Eq
let gt (o : order) : Prims.bool= o = Gt
let lt (o : order) : Prims.bool= o = Lt
let eq (o : order) : Prims.bool= o = Eq
let lex (o1 : order) (o2 : unit -> order) : order=
  match (o1, o2) with
  | (Lt, uu___) -> Lt
  | (Eq, uu___) -> o2 ()
  | (Gt, uu___) -> Gt
let order_from_int (i : Prims.int) : order=
  if i < Prims.int_zero then Lt else if i = Prims.int_zero then Eq else Gt
let compare_int (i : Prims.int) (j : Prims.int) : order=
  order_from_int (i - j)
let compare_bool (b1 : Prims.bool) (b2 : Prims.bool) : order=
  match (b1, b2) with
  | (false, true) -> Lt
  | (true, false) -> Gt
  | uu___ -> Eq
let rec compare_list :
  'a . 'a Prims.list -> 'a Prims.list -> ('a -> 'a -> order) -> order =
  fun l1 l2 f ->
    match (l1, l2) with
    | ([], []) -> Eq
    | ([], uu___) -> Lt
    | (uu___, []) -> Gt
    | (x::xs, y::ys) ->
        let uu___ = f x y in lex uu___ (fun uu___1 -> compare_list xs ys f)
let compare_option (f : 'a -> 'a -> order)
  (x : 'a FStar_Pervasives_Native.option)
  (y : 'a FStar_Pervasives_Native.option) : order=
  match (x, y) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> Eq
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___) -> Lt
  | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) -> Gt
  | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some y1) ->
      f x1 y1
