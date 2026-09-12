module IndexedSquash

module U8 = FStar.UInt8

type header = { tag: U8.t }

let is_big (h: header) : bool = U8.gt h.tag 127uy

noeq
type payload (h: header) =
  | Small : squash (is_big h == false) -> (v: U8.t) -> payload h
  | Big   : squash (is_big h == true)  -> (v: U8.t) -> payload h

let mk (h: header) : payload h =
  if is_big h then Big () 1uy else Small () 0uy

let parse (t: U8.t) : dtuple2 header (fun h -> payload h) =
  let h = { tag = t } in
  (| h, mk h |)

let value_of (t: U8.t) : U8.t =
  let (| _, p |) = parse t in
  match p with
  | Small _ v -> v
  | Big _ v -> v

let main () : FStar.All.ML FStar.Int32.t =
  if U8.eq (value_of 200uy) 1uy && U8.eq (value_of 3uy) 0uy then 0l else 1l
