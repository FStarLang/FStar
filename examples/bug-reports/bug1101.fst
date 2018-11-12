module Bug1101

open FStar.Exn


exception Ex1

let div a b =
  if b <> 0 then a/b else raise Ex1
