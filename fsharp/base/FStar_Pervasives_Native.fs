module FStar_Pervasives_Native
open Prims
type 'Aa option =
| None
| Some of 'Aa


let uu___is_None = function None -> true | _ -> false
let uu___is_Some = function Some _ -> true | _ -> false
let __proj__Some__item__v = function Some x -> x | _ -> failwith "Option value not available"
