(* -------------------------------------------------------------------- *)
module Impl = BatMap.PMap

(* -------------------------------------------------------------------- *)
type ('key, 'a) map = ('key, 'a) Impl.t

(* -------------------------------------------------------------------- *)
exception KeyNotFoundException

(* -------------------------------------------------------------------- *)
let empty () : ('key, 'a) map =
  Impl.create Pervasives.compare

(* -------------------------------------------------------------------- *)
let add (x : 'key) (v : 'a) (m : ('key, 'a) map) : ('key, 'a) map =
  Impl.add x v m

(* -------------------------------------------------------------------- *)
let remove (x : 'key) (m : ('key, 'a) map) : ('key, 'a) map =
  Impl.remove x m

(* -------------------------------------------------------------------- *)
let find (x : 'key) (m : ('key, 'a) map) : 'a =
  try  Impl.find x m
  with Not_found -> raise KeyNotFoundException

(* -------------------------------------------------------------------- *)
let contains (x : 'key) (m : ('key, 'a) map) : bool =
  Impl.mem x m
