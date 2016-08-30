module Hashtbl = Extlib.ExtHashtbl.Hashtbl

type ('a, 'b) t = ('a, 'b) Hashtbl.t

let create n = Hashtbl.create (Z.to_int n)

let find t k = Hashtbl.find t k

let mem t k = Hashtbl.mem t k

let add t k v =
  Hashtbl.add t k v; t
