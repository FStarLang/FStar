module FStar_Option
let isSome = function
  | Some _ -> true
  | None -> false
let isNone o = not (isSome o)
let map f = function
  | Some x -> Some (f x)
  | None -> None
let get = function
  | Some x -> x
  | None -> failwith "Option.get called on None"
