module Bug1948

type event op = x:op & int

type io_event = event int

let is_open1 (ev: io_event) : Tot prop = True

let rec is_open (evs: list io_event) : Tot prop =
  match evs with
  | [] -> True
  | h :: _ -> is_open1 h

let test0 () =
  let x : io_event = (| 17, 42 |) in
  assert (is_open [x])
