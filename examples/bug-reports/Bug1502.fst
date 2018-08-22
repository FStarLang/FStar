module Bug1502

#set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"

type ty =
  | TGhost
  | TBuffer

type arg = string * ty

let is_buffer arg :Tot bool = let _, ty = arg in TBuffer? ty

let rec liveness (args:list arg) :Tot string =
  let args = List.Tot.Base.filter is_buffer args in
  let rec aux args = "" in
  aux args

let disjoint (args:list arg) :Tot string = let args = List.Tot.Base.filter is_buffer args in ""
