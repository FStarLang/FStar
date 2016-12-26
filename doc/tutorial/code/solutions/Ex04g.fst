module Ex04g
//hd-tl

val hd : l:list 'a{Cons? l} -> Tot 'a
let hd l =
  match l with
  | h :: t -> h

val tl : l:list 'a{Cons? l} -> Tot (list 'a)
let tl l =
  match l with
  | h :: t -> t
