module HdTl

val hd : l:list 'a{is_Cons l} -> Tot 'a
let hd l =
  match l with
  | h :: t -> h

val tl : l:list 'a{is_Cons l} -> Tot (list 'a)
let tl l =
  match l with
  | h :: t -> t
