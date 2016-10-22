type heap = unit

(* https://www.lexifi.com/blog/references-physical-equality *)
type 'a ref = {
  mutable contents: 'a;
  id: int
}

type aref =
   | Ref of (unit * unit)

let emp =
  ()

