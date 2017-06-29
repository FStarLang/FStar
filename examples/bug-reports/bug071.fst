module Hd

val hd : l:list 'a{Cons? l} -> Tot 'a
let hd l = match l with
    | [] -> assert(false)
    | hd::tl -> hd 
