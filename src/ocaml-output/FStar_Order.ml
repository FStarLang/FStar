open Prims
type order =
  | Lt
  | Eq
  | Gt[@@deriving show]
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____4 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____8 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____12 -> false
let ge: order -> Prims.bool = fun o  -> o <> Lt
let le: order -> Prims.bool = fun o  -> o <> Gt
let ne: order -> Prims.bool = fun o  -> o <> Eq
let gt: order -> Prims.bool = fun o  -> o = Gt
let lt: order -> Prims.bool = fun o  -> o = Lt
let eq: order -> Prims.bool = fun o  -> o = Eq
let lex: order -> (Prims.unit -> order) -> order =
  fun o1  ->
    fun o2  ->
      match (o1, o2) with
      | (Lt ,uu____44) -> Lt
      | (Eq ,uu____49) -> o2 ()
      | (Gt ,uu____54) -> Gt
let order_from_int: Prims.int -> order =
  fun i  ->
    if i < (Prims.parse_int "0")
    then Lt
    else if i = (Prims.parse_int "0") then Eq else Gt
let compare_int: Prims.int -> Prims.int -> order =
  fun i  -> fun j  -> order_from_int (i - j)
let rec compare_list:
  'a . ('a -> 'a -> order) -> 'a Prims.list -> 'a Prims.list -> order =
  fun f  ->
    fun l1  ->
      fun l2  ->
        match (l1, l2) with
        | ([],[]) -> Eq
        | ([],uu____113) -> Lt
        | (uu____120,[]) -> Gt
        | (x::xs,y::ys) ->
            let uu____139 = f x y in
            lex uu____139 (fun uu____141  -> compare_list f xs ys)