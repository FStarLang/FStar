module Hello

open FStar.IO

let main = print_string "Hello F*!\n"

let foo (x:(x:int & (y:int{y > x}) & int)) :int = match x with
  | Mkdtuple3 x _ _ -> x
