
type 'a option' = 'a option =
  | None
  | Some of 'a[@@deriving yojson,show]

type 'a option = 'a option' =
  | None
  | Some of 'a[@@deriving yojson,show]

let uu___is_None = function None -> true | _ -> false
let uu___is_Some = function Some _ -> true | _ -> false
let __proj__Some__item__v = function Some x -> x | _ -> assert false

(* 'a * 'b *)
type ('a,'b) tuple2 = 'a * 'b[@@deriving yojson,show]

let fst = Stdlib.fst
let snd = Stdlib.snd

let __proj__Mktuple2__item___1 = fst
let __proj__Mktuple2__item___2 = snd
