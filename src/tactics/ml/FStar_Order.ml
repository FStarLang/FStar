open Prims
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____7 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____14 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____21 -> false
let ge: order -> Prims.bool =
  fun o  -> match o with | Lt  -> false | uu____28 -> true
let le: order -> Prims.bool =
  fun o  -> match o with | Gt  -> false | uu____35 -> true
let ne: order -> Prims.bool =
  fun o  -> match o with | Eq  -> false | uu____42 -> true
let gt: order -> Prims.bool =
  fun o  -> match o with | Gt  -> true | uu____49 -> false
let lt: order -> Prims.bool =
  fun o  -> match o with | Lt  -> true | uu____56 -> false
let eq: order -> Prims.bool =
  fun o  -> match o with | Eq  -> true | uu____63 -> false
let lex: order -> (Prims.unit -> order) -> order =
  fun o1  ->
    fun o2  ->
      match (o1, o2) with
      | (Lt ,uu____92) -> Lt
      | (Eq ,uu____97) -> o2 ()
      | (Gt ,uu____102) -> Gt
let order_from_int: Prims.int -> order =
  fun i  ->
    if i < (Prims.parse_int "0")
    then Lt
    else if i = (Prims.parse_int "0") then Eq else Gt
let compare_int: Prims.int -> Prims.int -> order =
  fun i  -> fun j  -> order_from_int (i - j)
let rec compare_list f l1 l2 =
  match (l1, l2) with
  | ([],[]) -> Eq
  | ([],uu____178) -> Lt
  | (uu____182,[]) -> Gt
  | (x::xs,y::ys) -> lex (f x y) (fun uu____194  -> compare_list f xs ys)