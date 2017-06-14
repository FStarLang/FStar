open Prims
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____6 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____12 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____18 -> false
let ge: order -> Prims.bool =
  fun o  -> match o with | Lt  -> false | uu____24 -> true
let le: order -> Prims.bool =
  fun o  -> match o with | Gt  -> false | uu____30 -> true
let ne: order -> Prims.bool =
  fun o  -> match o with | Eq  -> false | uu____36 -> true
let gt: order -> Prims.bool =
  fun o  -> match o with | Gt  -> true | uu____42 -> false
let lt: order -> Prims.bool =
  fun o  -> match o with | Lt  -> true | uu____48 -> false
let eq: order -> Prims.bool =
  fun o  -> match o with | Eq  -> true | uu____54 -> false
let lex: order -> (Prims.unit -> order) -> order =
  fun o1  ->
    fun o2  ->
      match (o1, o2) with
      | (Lt ,uu____81) -> Lt
      | (Eq ,uu____86) -> o2 ()
      | (Gt ,uu____91) -> Gt
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
  | ([],uu____160) -> Lt
  | (uu____164,[]) -> Gt
  | (x::xs,y::ys) -> lex (f x y) (fun uu____176  -> compare_list f xs ys)