type heap = unit

(* https://www.lexifi.com/blog/references-physical-equality *)
type 'a ref = {
  mutable contents: 'a;
  id: int
}
[@@deriving show]

type aref =
   | Ref of (unit * unit)
[@@deriving show]

let emp =
  ()

