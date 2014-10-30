
module Bug34

assume val g : 'a -> Tot 'b
assume val h : 'a:Type -> 'b:Type -> a:'a -> Tot (b:'b{b == g a})
