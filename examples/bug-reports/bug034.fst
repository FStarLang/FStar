module Bug034

assume val g : 'a -> Tot 'b
assume val h : a:Type -> b:Type{hasEq b} -> x:a -> Tot (y:b{y = g x})
assume val length: list 'a -> Tot int
assume val length_nil : unit -> Lemma
      (ensures (length [] = 0))
