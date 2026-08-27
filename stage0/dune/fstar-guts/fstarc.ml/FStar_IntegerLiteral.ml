open Prims
type int_base =
  | Dec 
  | Hex 
  | Oct 
  | Bin [@@deriving yojson,show]
let uu___is_Dec (projectee : int_base) : Prims.bool=
  match projectee with | Dec -> true | uu___ -> false
let uu___is_Hex (projectee : int_base) : Prims.bool=
  match projectee with | Hex -> true | uu___ -> false
let uu___is_Oct (projectee : int_base) : Prims.bool=
  match projectee with | Oct -> true | uu___ -> false
let uu___is_Bin (projectee : int_base) : Prims.bool=
  match projectee with | Bin -> true | uu___ -> false
