module Bug1784

type t = {
  x : int;
  y : int;
}

let foo (a:t) (x2 y2:int) =
  let {
    x = x1;
    y = y1;
  } = a in
  let b = {
    x = x2;
    y = y2;
  } in
  ()
