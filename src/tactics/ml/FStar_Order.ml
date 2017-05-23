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
let ge: order -> Prims.bool = fun o  -> o <> Lt
let le: order -> Prims.bool = fun o  -> o <> Gt
let ne: order -> Prims.bool = fun o  -> o <> Eq
let gt: order -> Prims.bool = fun o  -> o = Gt
let lt: order -> Prims.bool = fun o  -> o = Lt
let eq: order -> Prims.bool = fun o  -> o = Eq