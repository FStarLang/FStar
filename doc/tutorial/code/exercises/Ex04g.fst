module Ex04g
//hd-tl

val hd : l:list 'a{Cons? l} -> Tot 'a
val tl : l:list 'a{Cons? l} -> Tot (list 'a)
