module HdTl

val hd : l:list 'a{is_Cons l} -> Tot 'a
val tl : l:list 'a{is_Cons l} -> Tot (list 'a)
