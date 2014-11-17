
module Bug34

assume val g : 'a -> Tot 'b
assume val h : 'a:Type -> 'b:Type -> a:'a -> Tot (b:'b{b == g a})
assume val length: list 'a -> Tot int
assume val length_nil : unit -> Lemma
      (ensures (length int [] == 0))
